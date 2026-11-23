-- Prove2me | Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_cnorm_star
-- name    : Formalism.DivisionValues.OperatorNormFrames.cnorm_star
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:59.233429+00:00
-- url     : https://prove2.me/theorems/c3a5e957-566b-4de6-a778-1f3c3928053a
-- title:
--   Operator Norm Frames: cnorm star
-- statement:
--   The Operator Norm Frames construction uses the cnorm star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L22-L25

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

theorem Formalism.DivisionValues.OperatorNormFrames.cnorm_star {n : ℕ} (u : Fin n → ℂ) : Formalism.HermitianLatticesTheory.cnorm (star u) = Formalism.HermitianLatticesTheory.cnorm u := by sorry
