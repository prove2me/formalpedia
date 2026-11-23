-- Prove2me | Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_le_minOver
-- name    : Formalism.DivisionValues.OperatorNormFrames.le_minOver
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:46.94742+00:00
-- url     : https://prove2.me/theorems/d12cf228-b0a6-4cdc-85b1-3a5973eba73b
-- title:
--   Operator Norm Frames: le min Over
-- statement:
--   The Operator Norm Frames construction uses the le min Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L232-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L232-L236

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

theorem Formalism.DivisionValues.OperatorNormFrames.le_minOver {Ix : Type} [Fintype Ix] [Nonempty Ix] (f : Ix → ℝ) (a : ℝ) (h : ∀ p, a ≤ f p) :
    a ≤ minOver f := by sorry
