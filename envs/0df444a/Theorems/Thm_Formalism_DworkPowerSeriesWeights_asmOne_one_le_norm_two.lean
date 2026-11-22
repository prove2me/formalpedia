-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmOne_one_le_norm_two
-- name    : Formalism.DworkPowerSeriesWeights.asmOne_one_le_norm_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:15:43.295934+00:00
-- url     : https://prove2.me/theorems/36b24d03-4833-4b2a-b38a-83733b17b5da
-- title:
--   Dwork Power Series Weights: asm One one le norm two
-- statement:
--   The Dwork Power Series Weights construction uses the asm One one le norm two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/AsmOne.lean#L12-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/AsmOne.lean#L12-L35

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

theorem Formalism.DworkPowerSeriesWeights.asmOne_one_le_norm_two {K : Type u} [NormedField K] [IsUltrametricDist K] {l : ℕ}
    (hodd : Odd l) (hpi : ‖(l : K)‖ < 1) : 1 ≤ ‖(2 : K)‖ := by sorry
