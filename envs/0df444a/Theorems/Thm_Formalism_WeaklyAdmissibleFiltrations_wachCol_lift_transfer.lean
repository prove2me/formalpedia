-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_wachCol_lift_transfer
-- name    : Formalism.WeaklyAdmissibleFiltrations.wachCol_lift_transfer
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:39:04.94512+00:00
-- url     : https://prove2.me/theorems/e5e94514-dc4b-4328-884e-5721976cacc4
-- title:
--   Weakly Admissible Filtrations: wach Col lift transfer
-- statement:
--   The Weakly Admissible Filtrations construction uses the wach Col lift transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/WachCol.lean#L30-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/WachCol.lean#L30-L43

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_WachCol
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
variable {O X H : Type} [CommRing O] [AddCommGroup X] [Module O X] [AddCommGroup H] [Module O H]

theorem Formalism.WeaklyAdmissibleFiltrations.wachCol_lift_transfer (N I : Submodule O X) (f : N →ₗ[O] H) (Hf S : Submodule O H)
    (hr : LinearMap.range f = Hf) (hI : I.comap N.subtype = S.comap f) (a : O) :
    (∀ m ∈ N, a • m ∈ I) ↔ ∀ x ∈ Hf, a • x ∈ S := by sorry
