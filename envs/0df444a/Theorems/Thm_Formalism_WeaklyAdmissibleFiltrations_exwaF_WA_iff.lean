-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwaF_WA_iff
-- name    : Formalism.WeaklyAdmissibleFiltrations.exwaF_WA_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:39:31.445083+00:00
-- url     : https://prove2.me/theorems/f27d14ba-4d71-4a00-8c6d-73aaf3475dc1
-- title:
--   Weakly Admissible Filtrations: exwa F WA iff
-- statement:
--   The Weakly Admissible Filtrations construction uses the exwa F WA iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L236-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L236-L263

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

theorem Formalism.WeaklyAdmissibleFiltrations.exwaF_WA_iff (v : AddValuation LL (WithTop ℚ)) (c : LL) (hc : c ≠ 0) (r : ℚ)
    (hr : v c = (r : WithTop ℚ)) : (exwaF (n := n) c hc).WeaklyAdmissible v ↔ r = -1 := by sorry
