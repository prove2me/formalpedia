-- Prove2me | Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_star_dot_self
-- name    : Formalism.DivisionValues.OperatorNormFrames.star_dot_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:12.09629+00:00
-- url     : https://prove2.me/theorems/aff6cc4b-95eb-401d-9986-b2885d048076
-- title:
--   Operator Norm Frames: star dot self
-- statement:
--   The Operator Norm Frames construction uses the star dot self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L35-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L35-L48

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

theorem Formalism.DivisionValues.OperatorNormFrames.star_dot_self {n : ℕ} (w : Fin n → ℂ) :
    star w ⬝ᵥ w = ((Formalism.HermitianLatticesTheory.cnorm w ^ 2 : ℝ) : ℂ) := by sorry
