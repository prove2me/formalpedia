-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwa_val_det
-- name    : Formalism.WeaklyAdmissibleFiltrations.exwa_val_det
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:28:57.116646+00:00
-- url     : https://prove2.me/theorems/2d88484e-579f-4cea-9b01-358d0a9d118a
-- title:
--   Weakly Admissible Filtrations: exwa val det
-- statement:
--   The Weakly Admissible Filtrations construction uses the exwa val det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L134-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/ExwaFiltrationNegOneEqSpanSingle.lean#L134-L151

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

theorem Formalism.WeaklyAdmissibleFiltrations.exwa_val_det {M : Type} [AddCommGroup M] [Module LL M] [FiniteDimensional LL M]
    (v : AddValuation LL (WithTop ℚ)) (f : M →ₗ[LL] M) (k : ℕ) (hk : k ≠ 0)
    (hdim : finrank LL M = k) (c : LL) (r : ℚ) (hf : f ^ k = c • 1) (hc : v c = (r : WithTop ℚ)) :
    v (LinearMap.det f) = (r : WithTop ℚ) := by sorry
