-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwaPhi_pow_apply
-- name    : Formalism.WeaklyAdmissibleFiltrations.exwaPhi_pow_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:39:23.319476+00:00
-- url     : https://prove2.me/theorems/e8a899d8-e3bb-4d2b-8c0d-3ceadff2902a
-- title:
--   Weakly Admissible Filtrations: exwa Phi pow apply
-- statement:
--   The Weakly Admissible Filtrations construction uses the exwa Phi pow apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L106-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L106-L116

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

theorem Formalism.WeaklyAdmissibleFiltrations.exwaPhi_pow_apply (c : LL) (hc : c ≠ 0) (k : ℕ) (x : ZMod n → LL) :
    (((exwaPhi (n := n) c hc).toLinearMap ^ k) x) =
      c ^ k • fun i => x (i - k) := by sorry
