-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmOne_smul_wt
-- name    : Formalism.DworkPowerSeriesWeights.asmOne_smul_wt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:10.565363+00:00
-- url     : https://prove2.me/theorems/a7b3bd55-7808-4491-83ad-bf01d0d127e3
-- title:
--   Dwork Power Series Weights: asm One smul wt
-- statement:
--   The Dwork Power Series Weights construction uses the asm One smul wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/AsmOne.lean#L64-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/AsmOne.lean#L64-L73

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmOne
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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.asmOne_smul_wt {K : Type u} [NormedField K] {ι : Type v} {pi : ℝ} {r : ι → ℝ} {w : ℝ}
    {c : K} (hc : ‖c‖ ≤ 1) {f : MvPowerSeries ι K} (hf : WtGe pi r w f) :
    WtGe pi r w (c • f) := by sorry
