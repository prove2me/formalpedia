-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_jumpsIcc_and_subTopBot
-- name    : Formalism.WeaklyAdmissibleFiltrations.jumpsIcc_and_subTopBot
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:39:42.196806+00:00
-- url     : https://prove2.me/theorems/94d59d39-bc8b-486f-83b2-c4ce07d048b0
-- title:
--   Weakly Admissible Filtrations: jumps Icc and sub Top Bot
-- statement:
--   The Weakly Admissible Filtrations construction uses the jumps Icc and sub Top Bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/JumpsPFilAntitoneOfLe.lean#L86-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/JumpsPFilAntitoneOfLe.lean#L86-L86

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_JumpsPFilAntitoneOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open FilPhi

theorem Formalism.WeaklyAdmissibleFiltrations.jumpsIcc_and_subTopBot : JumpsIcc ∧ SubTopBot := by sorry
