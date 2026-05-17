open util/ordering[Date]

sig Date {}

abstract sig Bool {}
one sig True, False extends Bool {}

sig Customer {
  isActive: one Bool
}

sig Vehicle {
  status: one VehicleStatus,
  currentOdometer: one Int,
  lastServiceOdometer: one Int
}

abstract sig VehicleStatus {}
one sig Available, Booked, Maintenance, Retired extends VehicleStatus {}

sig Booking {
  customer: one Customer,
  vehicle: one Vehicle,
  pickupDate: one Date,
  returnDate: one Date,
  isActive: one Bool
}

-- Fact 1: Booking Date Ordering
fact BookingDateOrdering {
  all b: Booking |
    b.pickupDate != b.returnDate and
    b.pickupDate in prevs[b.returnDate]
}

-- Fact 2: Active Booking Implies Booked Vehicle
fact ActiveBookingImpliesBookedVehicle {
  all b: Booking |
    b.isActive = True =>
    b.vehicle.status = Booked
}

-- Fact 3: Booked Vehicle Has Active Booking
fact BookedVehicleHasActiveBooking {
  all v: Vehicle |
    v.status = Booked =>
    some b: Booking |
      b.vehicle = v and b.isActive = True
}

-- Fact 4: Customer Must Be Active For Booking
fact CustomerMustBeActive {
  all b: Booking |
    b.customer.isActive = True
}

-- Assertion 1: No Vehicle Can Be Booked And Available Simultaneously
assert NoVehicleBookedAndAvailable {
  no v: Vehicle |
    v.status = Booked and v.status = Available
}
check NoVehicleBookedAndAvailable for 10

-- Assertion 2: Maintenance Vehicles Cannot Have Active Bookings
assert MaintenanceExclusion {
  no v: Vehicle, b: Booking |
    v.status = Maintenance and
    b.vehicle = v and
    b.isActive = True
}
check MaintenanceExclusion for 10

-- Helper predicate for overlapping dates
pred overlaps[b1, b2: Booking] {
  b1.pickupDate in prevs[b2.returnDate] and
  b2.pickupDate in prevs[b1.returnDate]
}

-- Assertion 3: No Overlapping Active Bookings Same Vehicle
assert OverlapPrevention {
  no disj b1, b2: Booking |
    b1.vehicle = b2.vehicle and
    b1.isActive = True and
    b2.isActive = True and
    overlaps[b1, b2]
}
check OverlapPrevention for 10

-- Counterexample scenario
pred counterexampleScenario {
  some v: Vehicle, b: Booking |
    v.status = Maintenance and
    b.vehicle = v and
    b.isActive = True
}
run counterexampleScenario for 5