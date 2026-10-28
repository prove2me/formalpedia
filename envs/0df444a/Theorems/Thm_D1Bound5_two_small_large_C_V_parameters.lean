-- Prove2me | Theorems.Thm_D1Bound5_two_small_large_C_V_parameters
-- name    : D1Bound5.two_small_large_C_V_parameters
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:36:29.126622+00:00
-- url     : https://prove2.me/theorems/cf3c5717-5d0d-4612-910b-d69b21bfbb1f
-- title:
--   Two small large C V parameters
-- statement:
--   Auxiliary result `two_small_large_C_V_parameters` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/TwoSmallLargeCScalar.lean, lines 6-50, SHA-256 804f219a120af73973c5200ca150147c299fd63ae3573202fc4a1e60072c75cb. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

section
namespace D1Bound5

theorem _root_.D1Bound5.two_small_large_C_V_parameters
    (A B S T C D : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hB3 : B < 3)
    (hS : 3 ≤ S) (hST : S ≤ T) (hS8 : S < (10 : ℝ)^8) (hT8 : T < (10 : ℝ)^8)
    (hC : (10 : ℝ)^100 ≤ C) (hD : 2*S*T*C < D) :
    1000 ≤ C ∧ 4*T ≤ C ∧ 4*C ≤ D ∧
      32*B*S*T/A^3 ≤ C^2 ∧ 101*B^2*T^4/C < D := by sorry





end D1Bound5
end
