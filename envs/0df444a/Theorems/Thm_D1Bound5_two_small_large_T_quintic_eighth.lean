-- Prove2me | Theorems.Thm_D1Bound5_two_small_large_T_quintic_eighth
-- name    : D1Bound5.two_small_large_T_quintic_eighth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:06:34.572983+00:00
-- url     : https://prove2.me/theorems/05405c93-a74c-4078-a7f5-9b4b98d9d691
-- title:
--   Two small large T quintic eighth
-- statement:
--   Auxiliary result `two_small_large_T_quintic_eighth` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/TwoSmallLargeTScalar.lean, lines 108-141, SHA-256 1b6203efdcea0221de771d1a60328cc585980bd3f0ccf1c486409156e649ed47. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

section
namespace D1Bound5







theorem _root_.D1Bound5.two_small_large_T_quintic_eighth
    (A B S T C D : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hS : 0 < S)
    (hS8 : S < (10 : ℝ)^8) (hT : 0 < T)
    (hC : A^2*T^5/(37*S^2) < C) (hcross : A^3*B*T^3*C/(7*S) < D) :
    T^8/(10 : ℝ)^27 < D := by sorry

end D1Bound5
end
