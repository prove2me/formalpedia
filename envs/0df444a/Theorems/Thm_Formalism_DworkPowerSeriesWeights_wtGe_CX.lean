-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_wtGe_CX
-- name    : Formalism.DworkPowerSeriesWeights.wtGe_CX
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:15:28.920964+00:00
-- url     : https://prove2.me/theorems/5e46e0e1-91f8-4941-8466-92e70f9f75f2
-- title:
--   Dwork Power Series Weights: wt Ge CX
-- statement:
--   The Dwork Power Series Weights construction uses the wt Ge CX property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/PureCrossTermWeight.lean#L33-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/PureCrossTermWeight.lean#L33-L45

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

theorem Formalism.DworkPowerSeriesWeights.wtGe_CX {pi : ℝ} (h0 : 0 < pi) (r : ι → ℝ) (i : ι) {c : K} (hc : ‖c‖ ≤ 1) :
    WtGe pi r (r i) (MvPowerSeries.C c * MvPowerSeries.X i) := by sorry
