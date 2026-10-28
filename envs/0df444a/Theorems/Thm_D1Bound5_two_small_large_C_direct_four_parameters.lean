-- Prove2me | Theorems.Thm_D1Bound5_two_small_large_C_direct_four_parameters
-- name    : D1Bound5.two_small_large_C_direct_four_parameters
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:32:42.014779+00:00
-- url     : https://prove2.me/theorems/17977db8-14ce-46b8-8c1f-8b3ff55199f6
-- title:
--   Two small large C direct four parameters
-- statement:
--   Auxiliary result `two_small_large_C_direct_four_parameters` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/TwoSmallLargeCScalar.lean, lines 52-89, SHA-256 804f219a120af73973c5200ca150147c299fd63ae3573202fc4a1e60072c75cb. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

section
namespace D1Bound5



theorem _root_.D1Bound5.two_small_large_C_direct_four_parameters
    (A B S T C D : ℝ) (hA : 1 ≤ A) (hAB : A ≤ B) (hB : 0 < B) (hB3 : B < 3)
    (hS : 0 < S) (hT : 0 < T) (hS8 : S < (10 : ℝ)^8) (hT8 : T < (10 : ℝ)^8)
    (hC : (10 : ℝ)^100 ≤ C) (hV : (2/5 : ℝ)*A^2*C^5/T^2 < D) :
    1000*C ≤ D ∧ 17*A*B*S*T*C^3 ≤ D := by sorry



end D1Bound5
end
