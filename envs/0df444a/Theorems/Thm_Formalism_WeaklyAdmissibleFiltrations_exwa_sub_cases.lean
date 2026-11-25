-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwa_sub_cases
-- name    : Formalism.WeaklyAdmissibleFiltrations.exwa_sub_cases
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:39:42.673612+00:00
-- url     : https://prove2.me/theorems/5e77a5d9-762a-4300-ae3d-3b5e87ad7795
-- title:
--   Weakly Admissible Filtrations: exwa sub cases
-- statement:
--   The Weakly Admissible Filtrations construction uses the exwa sub cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L194-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L194-L234

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

theorem Formalism.WeaklyAdmissibleFiltrations.exwa_sub_cases (c : LL) (hc : c ≠ 0) (D' : Submodule LL (ZMod n → LL))
    (hD : (exwaF c hc).IsSub D') : D' = ⊥ ∨ D' = ⊤ := by sorry
