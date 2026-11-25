-- Prove2me | Theorems.Thm_Formalism_ExtensionFiltration_mk_lt
-- name    : Formalism.ExtensionFiltration.mk_lt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:27:42.372782+00:00
-- url     : https://prove2.me/theorems/3b02f4b9-25c7-4067-866d-72ed21798782
-- title:
--   Extension Filtration: mk lt
-- statement:
--   The Extension Filtration construction uses the mk lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/GlobalBoundRefinements.lean#L148-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/GlobalBoundRefinements.lean#L148-L193

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_CovolumeEstimateAnchoredWeights
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeAssemblyHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeFullAssemblyHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeIntoDivisionHolds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_SpanMuMin
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_TwistLower
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_MuMaxMinkowski
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GlobalBoundRefinements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ExtensionFiltration
noncomputable section
open Module NumberField
open Formalism.HN
open NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped ENNReal NNReal nonZeroDivisors

theorem Formalism.ExtensionFiltration.mk_lt (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (g : InfinitePlace K → ℝ) (hg : ∀ w, 0 < g w)
    (h : (FractionalIdeal.absNorm I.1 : ℝ) * (2:ℝ) ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| <
      Real.pi ^ nrComplexPlaces K * ∏ w, g w ^ 2) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧ ∀ w : InfinitePlace K, w a < g w := by sorry
