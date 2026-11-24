-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwaF_val_det_top
-- name    : Formalism.WeaklyAdmissibleFiltrations.exwaF_val_det_top
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:39:22.434856+00:00
-- url     : https://prove2.me/theorems/53ed1d94-7c75-4a1b-8d1c-78f2a4e20ffa
-- title:
--   Weakly Admissible Filtrations: exwa F val det top
-- statement:
--   The Weakly Admissible Filtrations construction uses the exwa F val det top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L181-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L181-L192

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

theorem Formalism.WeaklyAdmissibleFiltrations.exwaF_val_det_top (v : AddValuation LL (WithTop ℚ)) (c : LL) (hc : c ≠ 0) (r : ℚ)
    (hr : v c = (r : WithTop ℚ)) (h : ∀ x ∈ (⊤ : Submodule LL (ZMod n → LL)),
      (exwaF (n := n) c hc).φ x ∈ (⊤ : Submodule LL (ZMod n → LL))) :
    v (LinearMap.det ((exwaF (n := n) c hc).φres ⊤ h)) = (((n : ℚ) * r : ℚ) : WithTop ℚ) := by sorry
