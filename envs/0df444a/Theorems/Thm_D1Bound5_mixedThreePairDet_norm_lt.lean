-- Prove2me | Theorems.Thm_D1Bound5_mixedThreePairDet_norm_lt
-- name    : D1Bound5.mixedThreePairDet_norm_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:16.917797+00:00
-- url     : https://prove2.me/theorems/82a08e6b-1733-4efa-9305-e7f0b195b2a6
-- title:
--   Mixed Three Pair Det norm lt
-- statement:
--   The three-pair determinant polynomial remains uniformly small with the asymmetric first-row/later-row perturbations.
-- source:
--   D1Bound5/MixedFourDetBound.lean, lines 47-115, SHA-256 863a07b764253ce476290edc497efddecf3c39545921323e93756d8912d3da78. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open Matrix

namespace D1Bound5




theorem _root_.D1Bound5.mixedThreePairDet_norm_lt (P Q R : ℂ)
    (hP : ‖P - (1/4 : ℂ)‖ < (7/192 : ℝ))
    (hQ : ‖Q - (1/4 : ℂ)‖ < (7/192 : ℝ))
    (hR : ‖R - (1/4 : ℂ)‖ < (7/192 : ℝ)) :
    ‖P^2 + Q^2 + R^2 - 2*(P*Q + P*R + Q*R)‖ < (3/10 : ℝ) := by sorry



end D1Bound5

namespace D1Bound5



end D1Bound5

namespace D1Bound5



end D1Bound5
end
