-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_congr
-- name    : Formalism.DworkPowerSeriesWeights.wtGe_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:10.593294+00:00
-- url     : https://prove2.me/theorems/a1b5beb8-2141-44fe-8e64-8f9d88d61669
-- title:
--   Dwork Power Series Weights: wt Ge congr
-- statement:
--   The Dwork Power Series Weights construction uses the wt Ge congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/PureCrossTermWeight.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/PureCrossTermWeight.lean#L17-L20

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

theorem Formalism.DworkPowerSeriesWeights.wtGe_congr {pi : ℝ} {r : ι → ℝ} {wt wt' : ℝ} (h : wt = wt') {f : MvPowerSeries ι K}
    (hf : WtGe pi r wt f) : WtGe pi r wt' f := by sorry
