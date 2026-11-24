-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwaF_e
-- name    : Formalism.WeaklyAdmissibleFiltrations.exwaF_e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:39:23.037174+00:00
-- url     : https://prove2.me/theorems/58f60767-7cd7-4e41-b30f-c0255a40e1ba
-- title:
--   Weakly Admissible Filtrations: exwa F e
-- statement:
--   The Weakly Admissible Filtrations construction uses the exwa F e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L168-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L168-L168

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_ExwaFiltrationNegOneEqSpanSingle
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
variable {LL : Type} [Field LL] {n : ℕ} [NeZero n]

theorem Formalism.WeaklyAdmissibleFiltrations.exwaF_e (c : LL) (hc : c ≠ 0) : (exwaF (n := n) c hc).e = 1 := by sorry
