-- Prove2me | Theorems.Thm_D1Bound5_two_small_large_T_quadratic_parameters
-- name    : D1Bound5.two_small_large_T_quadratic_parameters
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:34:36.097383+00:00
-- url     : https://prove2.me/theorems/e55e0498-460b-4641-8e62-e0704fc4d250
-- title:
--   Two small large T quadratic parameters
-- statement:
--   Auxiliary result `two_small_large_T_quadratic_parameters` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/TwoSmallLargeTScalar.lean, lines 24-82, SHA-256 1b6203efdcea0221de771d1a60328cc585980bd3f0ccf1c486409156e649ed47. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

section
namespace D1Bound5



theorem _root_.D1Bound5.two_small_large_T_quadratic_parameters
    (A B S T C D : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hB3 : B < 3)
    (hS : 3 ≤ S) (hT : (10 : ℝ)^72 ≤ T)
    (hC : 5*A*B*S*T^2 < C) (hD : 2*S*T*C < D) :
    1000 ≤ C ∧ 4*T ≤ C ∧ 4*C ≤ D ∧
      32*B*S*T/A^3 ≤ C^2 ∧ 101*B^2*T^4/C < D := by sorry





end D1Bound5
end
