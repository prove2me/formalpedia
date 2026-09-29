-- Prove2me | solution 1 for flt5_5dvd_phi5_of_5dvd_sum
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T07:14:12.496859+00:00
-- url     : https://prove2.me/submissions/fd0922bc-cfe3-4ed4-80c3-f06fd6263a24

import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

-- If 5|(a+b) then 5|Phi5(a,b).
-- In ZMod 5: if x+y=0 then x^4-x^3y+x^2y^2-xy^3+y^4=0 (by decide).

theorem solution (a b : ℤ) (h5ab : (5 : ℤ) ∣ a + b) :
    (5 : ℤ) ∣ a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 := by
  have key : ∀ (x y : ZMod 5), x + y = 0 →
      x ^ 4 - x ^ 3 * y + x ^ 2 * y ^ 2 - x * y ^ 3 + y ^ 4 = 0 := by decide
  have hab : ((a + b : ℤ) : ZMod 5) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (a + b) 5).mpr h5ab
  have hphi : ((a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 : ℤ) : ZMod 5) = 0 := by
    push_cast at hab ⊢
    exact key _ _ hab
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp hphi
