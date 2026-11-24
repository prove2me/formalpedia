-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_subTopBot
-- name    : Formalism.WeaklyAdmissibleFiltrations.subTopBot
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:39:56.666778+00:00
-- url     : https://prove2.me/theorems/43c48ca4-8dbd-4416-a3fb-0a6ae4d2dc0f
-- title:
--   Weakly Admissible Filtrations: sub Top Bot
-- statement:
--   The Weakly Admissible Filtrations construction uses the sub Top Bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/JumpsPFilAntitoneOfLe.lean#L75-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/JumpsPFilAntitoneOfLe.lean#L75-L84

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

theorem Formalism.WeaklyAdmissibleFiltrations.subTopBot : SubTopBot := by sorry
