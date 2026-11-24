-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_negativeJumpsSum_holds
-- name    : Formalism.WeaklyAdmissibleFiltrations.negativeJumpsSum_holds
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:39:26.479174+00:00
-- url     : https://prove2.me/theorems/52bb6315-3460-4832-a857-19117f58920e
-- title:
--   Weakly Admissible Filtrations: negative Jumps Sum holds
-- statement:
--   The Weakly Admissible Filtrations construction uses the negative Jumps Sum holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/NegJumps.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/NegJumps.lean#L23-L27

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_DpcrisStable
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_NegJumps
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
open Module

theorem Formalism.WeaklyAdmissibleFiltrations.negativeJumpsSum_holds : NegJumps := by sorry
