-- Prove2me | Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_wachModule_mem_cocycles_iff
-- name    : Formalism.WeaklyAdmissibleFiltrations.wachModule_mem_cocycles_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:30:13.348307+00:00
-- url     : https://prove2.me/theorems/a3777b64-b0ad-4f47-b03a-0d34af9e5322
-- title:
--   Weakly Admissible Filtrations: wach Module mem cocycles iff
-- statement:
--   The Weakly Admissible Filtrations construction uses the wach Module mem cocycles iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/WachCol.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CrystallineStableLifts/WachCol.lean#L55-L59

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
open Formalism.CoboundaryTransfers
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {Bw : Base O A} {M : ℕ}
  {D D' : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  [AddCommGroup D'] [Module A D'] [Module O D'] [IsScalarTower O A D']

theorem Formalism.WeaklyAdmissibleFiltrations.wachModule_mem_cocycles_iff (W : WachMod Bw M D) (pr : D × D) :
    pr ∈ W.Z1 ↔ (W.γ pr.1 - pr.1) - (W.φ pr.2 - pr.2) = 0 := by sorry
