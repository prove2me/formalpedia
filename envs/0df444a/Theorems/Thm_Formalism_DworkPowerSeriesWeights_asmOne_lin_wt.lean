-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmOne_lin_wt
-- name    : Formalism.DworkPowerSeriesWeights.asmOne_lin_wt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:59:08.39652+00:00
-- url     : https://prove2.me/theorems/06f96e7c-b993-43e4-9ce3-06a5533c6cd1
-- title:
--   Dwork Power Series Weights: asm One lin wt
-- statement:
--   The Dwork Power Series Weights construction uses the asm One lin wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/AsmOne.lean#L37-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/AsmOne.lean#L37-L58

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

theorem Formalism.DworkPowerSeriesWeights.asmOne_lin_wt {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v} [Fintype ι]
    {pi : ℝ} (h0 : 0 < pi) (c : ι → K) (hc : ∀ i, ‖c i‖ ≤ 1) (t : ℝ) :
    WtGe pi (fun _ : ι => t) t (∑ i, MvPowerSeries.C (c i) * MvPowerSeries.X i) := by sorry
