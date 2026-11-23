-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmOne_lin_const
-- name    : Formalism.DworkPowerSeriesWeights.asmOne_lin_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:59:14.522142+00:00
-- url     : https://prove2.me/theorems/4a85bac3-ed60-4185-a93e-abb04229d1f0
-- title:
--   Dwork Power Series Weights: asm One lin const
-- statement:
--   The Dwork Power Series Weights construction uses the asm One lin const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/AsmOne.lean#L60-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/AsmOne.lean#L60-L62

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

theorem Formalism.DworkPowerSeriesWeights.asmOne_lin_const {K : Type u} [NormedField K] {ι : Type v} [Fintype ι] (c : ι → K) :
    MvPowerSeries.constantCoeff (∑ i, MvPowerSeries.C (c i) * MvPowerSeries.X i) = 0 := by sorry
