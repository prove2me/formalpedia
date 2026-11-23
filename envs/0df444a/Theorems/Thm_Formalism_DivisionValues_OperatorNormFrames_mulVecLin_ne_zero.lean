-- Prove2me | Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_mulVecLin_ne_zero
-- name    : Formalism.DivisionValues.OperatorNormFrames.mulVecLin_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:34.892378+00:00
-- url     : https://prove2.me/theorems/890a665b-f8d9-414f-bd8f-a0594598f422
-- title:
--   Operator Norm Frames: mul Vec Lin ne zero
-- statement:
--   The Operator Norm Frames construction uses the mul Vec Lin ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L461-L467
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L461-L467

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
open OperatorNormFrames
open Formalism.DivisionValues.OperatorNormFrames

theorem Formalism.DivisionValues.OperatorNormFrames.mulVecLin_ne_zero {K : Type} [Field K] {a b : ℕ} (N : Matrix (Fin b) (Fin a) K) (h : N ≠ 0) :
    Matrix.mulVecLin N ≠ 0 := by sorry
