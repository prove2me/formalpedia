-- Prove2me | Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_mul_inv_mulVec
-- name    : Formalism.DivisionValues.OperatorNormFrames.mul_inv_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:51.206088+00:00
-- url     : https://prove2.me/theorems/4c708a14-11f7-41b1-a6af-25bc4fd723c1
-- title:
--   Operator Norm Frames: mul inv mul Vec
-- statement:
--   The Operator Norm Frames construction uses the mul inv mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L118-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L118-L120

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

theorem Formalism.DivisionValues.OperatorNormFrames.mul_inv_mulVec {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (hY : IsUnit Y.det) (x : Fin n → ℂ) :
    Y.mulVec (Y⁻¹.mulVec x) = x := by sorry
