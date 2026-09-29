-- Prove2me | solution 1 for flt7_phi7_minus_7a6_dvd_apb
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T08:35:15.564412+00:00
-- url     : https://prove2.me/submissions/3cc61dbe-5a95-46b9-9837-62b65bb19302

import Mathlib.NumberTheory.Multiplicity

-- Key algebraic identity: (a+b) divides (Phi7(a,b) - 7*a^6) in ℤ.
-- Proof: Phi7(a,b) - 7*a^6 = (a+b) * (-6a^5 + 5a^4b - 4a^3b^2 + 3a^2b^3 - 2ab^4 + b^5).
-- This follows from Phi7(a,-a) = 7*a^6 (b ≡ -a mod a+b), hence Phi7(a,b) ≡ 7*a^6 mod (a+b).
theorem solution (a b : ℤ) :
    (a + b) ∣ (a^6 - a^5*b + a^4*b^2 - a^3*b^3 + a^2*b^4 - a*b^5 + b^6 - 7*a^6) :=
  ⟨-6*a^5 + 5*a^4*b - 4*a^3*b^2 + 3*a^2*b^3 - 2*a*b^4 + b^5, by ring⟩
