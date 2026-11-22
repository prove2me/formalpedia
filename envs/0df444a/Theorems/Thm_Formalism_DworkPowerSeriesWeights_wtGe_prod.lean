-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_prod
-- name    : Formalism.DworkPowerSeriesWeights.wtGe_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:47.979287+00:00
-- url     : https://prove2.me/theorems/72891fb1-ee57-426f-872e-b659b32f84b2
-- title:
--   Dwork Power Series Weights: wt Ge prod
-- statement:
--   The Dwork Power Series Weights construction uses the wt Ge prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SubstitutionWeightBound.lean#L76-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SubstitutionWeightBound.lean#L76-L79

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WtGeProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
variable {K : Type u} [NormedField K] {ι : Type v}
variable [IsUltrametricDist K]

theorem Formalism.DworkPowerSeriesWeights.wtGe_prod {pi : ℝ} (h0 : 0 < pi) {r : ι → ℝ} {α : Type w} (s : Finset α) (wt : α → ℝ)
    (F : α → MvPowerSeries ι K) (h : ∀ i ∈ s, WtGe pi r (wt i) (F i)) :
    WtGe pi r (∑ i ∈ s, wt i) (∏ i ∈ s, F i) := by sorry
