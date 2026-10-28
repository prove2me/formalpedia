-- Prove2me | Theorems.Thm_D1Bound5_mixedThreePairDet_norm_lt_33_128
-- name    : D1Bound5.mixedThreePairDet_norm_lt_33_128
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:52:40.186704+00:00
-- url     : https://prove2.me/theorems/f4936729-a71e-4d8c-be5d-bbdc49fc1506
-- title:
--   Mixed Three Pair Det norm lt 33 128
-- statement:
--   The sharper determinant threshold used in Lemma product-five. It improves the previously established 3/10 bound using the exact nine-term quadratic estimate rather than a 13-term majorant.
-- source:
--   D1Bound5/ProductFivePrefixDet.lean, lines 65-104, SHA-256 f9937f549ad5792258cef7e7ac08638bae75b2a7351c4bdd51aa581d8bdd481f. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.mixedThreePairDet_norm_lt_33_128 (P Q R : ℂ)
    (hP : ‖P - (1/4 : ℂ)‖ < (7/192 : ℝ))
    (hQ : ‖Q - (1/4 : ℂ)‖ < (7/192 : ℝ))
    (hR : ‖R - (1/4 : ℂ)‖ < (7/192 : ℝ)) :
    ‖P^2 + Q^2 + R^2 - 2*(P*Q + P*R + Q*R)‖ <
      (33/128 : ℝ) := by sorry





end D1Bound5
end
