-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwa_restrict_pow_coe
-- name    : Formalism.WeaklyAdmissibleFiltrations.exwa_restrict_pow_coe
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:39:44.052804+00:00
-- url     : https://prove2.me/theorems/52a89397-601f-4535-8b46-14bf43d691dd
-- title:
--   Weakly Admissible Filtrations: exwa restrict pow coe
-- statement:
--   The Weakly Admissible Filtrations construction uses the exwa restrict pow coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L153-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L153-L160

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
variable {LL : Type} [Field LL]

theorem Formalism.WeaklyAdmissibleFiltrations.exwa_restrict_pow_coe {M : Type} [AddCommGroup M] [Module LL M] (f : M →ₗ[LL] M)
    (p : Submodule LL M) (h : ∀ x ∈ p, f x ∈ p) (k : ℕ) (x : p) :
    (((f.restrict h) ^ k) x : M) = (f ^ k) x := by sorry
