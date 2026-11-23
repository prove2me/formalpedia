-- Prove2me | Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_nrm_mul_le
-- name    : Formalism.DivisionValues.OperatorNormFrames.nrm_mul_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:20.594841+00:00
-- url     : https://prove2.me/theorems/5f8ad895-5568-4c05-874b-431ab71c34a2
-- title:
--   Operator Norm Frames: nrm mul le
-- statement:
--   The Operator Norm Frames construction uses the nrm mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L440-L449
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L440-L449

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

theorem Formalism.DivisionValues.OperatorNormFrames.nrm_mul_le {a b c : ℕ} (A : Matrix (Fin c) (Fin b) ℂ) (B : Matrix (Fin b) (Fin a) ℂ) :
    nrm (A * B) ≤ nrm A * nrm B := by sorry
