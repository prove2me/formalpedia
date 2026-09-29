-- Prove2me | solution 1 for flt7_dvd_7a6_of_dvd_apb_phi7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T08:35:15.929983+00:00
-- url     : https://prove2.me/submissions/fdede307-28df-4a87-a6c5-97ea8b3571a7

import Mathlib.NumberTheory.Multiplicity

-- If q | (a+b) and q | Phi7(a,b), then q | 7*a^6.
-- Proof: from (a+b) | (Phi7(a,b) - 7*a^6), and q | (a+b), we get q | (Phi7 - 7*a^6).
-- Then q | Phi7 and q | (Phi7 - 7*a^6) implies q | 7*a^6.
theorem solution (a b q : ℤ) (hqab : q ∣ a + b)
    (hqphi : q ∣ a^6 - a^5*b + a^4*b^2 - a^3*b^3 + a^2*b^4 - a*b^5 + b^6) :
    q ∣ 7 * a^6 := by
  have hident : (a + b) ∣ (a^6 - a^5*b + a^4*b^2 - a^3*b^3 + a^2*b^4 - a*b^5 + b^6 - 7*a^6) :=
    ⟨-6*a^5 + 5*a^4*b - 4*a^3*b^2 + 3*a^2*b^3 - 2*a*b^4 + b^5, by ring⟩
  have h1 : q ∣ a^6 - a^5*b + a^4*b^2 - a^3*b^3 + a^2*b^4 - a*b^5 + b^6 - 7*a^6 :=
    dvd_trans hqab hident
  have h2 : q ∣ (a^6 - a^5*b + a^4*b^2 - a^3*b^3 + a^2*b^4 - a*b^5 + b^6) -
             (a^6 - a^5*b + a^4*b^2 - a^3*b^3 + a^2*b^4 - a*b^5 + b^6 - 7*a^6) :=
    dvd_sub hqphi h1
  convert h2 using 1; ring
