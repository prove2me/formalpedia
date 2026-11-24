-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwaPhi_pow_n
-- name    : Formalism.WeaklyAdmissibleFiltrations.exwaPhi_pow_n
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:29:18.135993+00:00
-- url     : https://prove2.me/theorems/8aa643a7-6f16-4daa-be87-c813a5e8fc84
-- title:
--   Weakly Admissible Filtrations: exwa Phi pow n
-- statement:
--   The Weakly Admissible Filtrations construction uses the exwa Phi pow n property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L118-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L118-L122

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

theorem Formalism.WeaklyAdmissibleFiltrations.exwaPhi_pow_n (c : LL) (hc : c ≠ 0) :
    (exwaPhi (n := n) c hc).toLinearMap ^ n = c ^ n • 1 := by sorry
