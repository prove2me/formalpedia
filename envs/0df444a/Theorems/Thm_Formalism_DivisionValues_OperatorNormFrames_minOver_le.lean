-- Prove2me | Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_minOver_le
-- name    : Formalism.DivisionValues.OperatorNormFrames.minOver_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:48.09247+00:00
-- url     : https://prove2.me/theorems/eee0f740-1a34-4b87-b03b-88cdb2ec8096
-- title:
--   Operator Norm Frames: min Over le
-- statement:
--   The Operator Norm Frames construction uses the min Over le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L223-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L223-L226

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

theorem Formalism.DivisionValues.OperatorNormFrames.minOver_le {Ix : Type} [Fintype Ix] [Nonempty Ix] (f : Ix → ℝ) (p : Ix) : minOver f ≤ f p := by sorry
