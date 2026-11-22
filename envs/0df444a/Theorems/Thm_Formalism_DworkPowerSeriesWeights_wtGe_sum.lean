-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_sum
-- name    : Formalism.DworkPowerSeriesWeights.wtGe_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:03.116318+00:00
-- url     : https://prove2.me/theorems/b48bb9d5-2e48-4f06-8b7e-4e453391e8c4
-- title:
--   Dwork Power Series Weights: wt Ge sum
-- statement:
--   The Dwork Power Series Weights construction uses the wt Ge sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SubstitutionWeightBound.lean#L52-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SubstitutionWeightBound.lean#L52-L58

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

theorem Formalism.DworkPowerSeriesWeights.wtGe_sum {pi : ℝ} (h0 : 0 < pi) {r : ι → ℝ} {wt : ℝ} {α : Type w} (s : Finset α)
    (F : α → MvPowerSeries ι K) (h : ∀ i ∈ s, WtGe pi r wt (F i)) :
    WtGe pi r wt (∑ i ∈ s, F i) := by sorry
