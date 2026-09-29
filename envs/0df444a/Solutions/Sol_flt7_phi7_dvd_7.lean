-- Prove2me | solution 1 for flt7_phi7_dvd_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T07:49:01.413569+00:00
-- url     : https://prove2.me/submissions/7e64de96-3990-46f4-ba46-4b5213a9527c

import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

-- If 7 | (a+b) for integers a, b, then 7 | Phi7(a,b)
-- where Phi7(a,b) = a^6 - a^5*b + a^4*b^2 - a^3*b^3 + a^2*b^4 - a*b^5 + b^6.
-- Proof: in ZMod 7, if a+b=0 then b=-a, so Phi7(a,-a) = 7*a^6 = 0.
theorem solution (a b : ℤ) (h7ab : (7:ℤ) ∣ a + b) :
    (7:ℤ) ∣ a^6 - a^5*b + a^4*b^2 - a^3*b^3 + a^2*b^4 - a*b^5 + b^6 := by
  have hkey : ∀ (x y : ZMod 7), x + y = 0 →
      x^6 - x^5*y + x^4*y^2 - x^3*y^3 + x^2*y^4 - x*y^5 + y^6 = 0 := by decide
  have hab0 : (a : ZMod 7) + (b : ZMod 7) = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (a + b) 7).mpr h7ab
    push_cast at h; exact h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp (by push_cast; exact hkey _ _ hab0)
