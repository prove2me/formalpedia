-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmOne_smul_const
-- name    : Formalism.DworkPowerSeriesWeights.asmOne_smul_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:06.308501+00:00
-- url     : https://prove2.me/theorems/d96db339-4cd1-4d7e-abf4-0aab2ae66fda
-- title:
--   Dwork Power Series Weights: asm One smul const
-- statement:
--   The Dwork Power Series Weights construction uses the asm One smul const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/AsmOne.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/AsmOne.lean#L75-L80

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

theorem Formalism.DworkPowerSeriesWeights.asmOne_smul_const {K : Type u} [NormedField K] {ι : Type v} (c : K)
    {f : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (c • f) = 0 := by sorry
