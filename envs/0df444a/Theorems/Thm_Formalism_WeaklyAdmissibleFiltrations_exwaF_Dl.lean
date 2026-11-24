-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwaF_Dl
-- name    : Formalism.WeaklyAdmissibleFiltrations.exwaF_Dl
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:39:18.551287+00:00
-- url     : https://prove2.me/theorems/b824c9f3-8661-4c0e-9af3-7a7e77302844
-- title:
--   Weakly Admissible Filtrations: exwa F Dl
-- statement:
--   The Weakly Admissible Filtrations construction uses the exwa F Dl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L65-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L65-L66

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

theorem Formalism.WeaklyAdmissibleFiltrations.exwaF_Dl (c : LL) (hc : c ≠ 0) (i : ZMod n) :
    (exwaF c hc).Dl i = LL ∙ (Pi.single i (1 : LL) : ZMod n → LL) := by sorry
