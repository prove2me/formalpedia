-- Prove2me | Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_opNorm_le_iff
-- name    : Formalism.DivisionValues.OperatorNormFrames.opNorm_le_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:32.565303+00:00
-- url     : https://prove2.me/theorems/1612df40-f7a0-42a7-9e36-e79fc4f94c6b
-- title:
--   Operator Norm Frames: op Norm le iff
-- statement:
--   The Operator Norm Frames construction uses the op Norm le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L50-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L50-L80

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.OperatorNormFrames

theorem Formalism.DivisionValues.OperatorNormFrames.opNorm_le_iff {a D : ℕ} (A : Matrix (Fin D) (Fin a) ℂ) (c : ℝ) (hc : 0 ≤ c) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖ ≤ c ↔
      ∀ (x : Fin a → ℂ) (y : Fin D → ℂ),
        ‖y ⬝ᵥ A.mulVec x‖ ≤ c * Formalism.HermitianLatticesTheory.cnorm x * Formalism.HermitianLatticesTheory.cnorm y := by sorry
