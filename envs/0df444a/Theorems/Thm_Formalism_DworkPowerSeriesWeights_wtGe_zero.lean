-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_zero
-- name    : Formalism.DworkPowerSeriesWeights.wtGe_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:16:08.550434+00:00
-- url     : https://prove2.me/theorems/77d797d5-7197-433f-88d6-e0f850f89c7e
-- title:
--   Dwork Power Series Weights: wt Ge zero
-- statement:
--   The Dwork Power Series Weights construction uses the wt Ge zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/PureCrossTermWeight.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/PureCrossTermWeight.lean#L22-L27

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_PureCrossTermWeight
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
open Formalism.IncomingBounds
variable {K : Type u} [NormedField K] {ι : Type v}

theorem Formalism.DworkPowerSeriesWeights.wtGe_zero {pi : ℝ} (h0 : 0 < pi) (r : ι → ℝ) (wt : ℝ) :
    WtGe pi r wt (0 : MvPowerSeries ι K) := by sorry
