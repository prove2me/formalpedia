-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_Lat2_dualLat_span
-- name    : Formalism.RepresentationBoundsCohomology.LOC.Lat2.dualLat_span
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:26:12.013996+00:00
-- url     : https://prove2.me/theorems/3fbda4a7-8fc9-47fc-92a2-63ed5f431f9b
-- title:
--   Lat2: dual Lat span
-- statement:
--   The Lat2 construction uses the dual Lat span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/ExistsBasisOfLattice.lean#L93-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/ExistsBasisOfLattice.lean#L93-L110

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_StatDualFibreLattice
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_ExistsBasisOfLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
open Module
open Formalism.RepresentationBoundsCohomology.LOC.Lat2
variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {V V' : Type u} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
  [IsScalarTower O (FractionRing O) V] [AddCommGroup V'] [Module O V'] [Module (FractionRing O) V']
  [IsScalarTower O (FractionRing O) V']
omit [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]

theorem Formalism.RepresentationBoundsCohomology.LOC.Lat2.dualLat_span {b : V →ₗ[O] V' →ₗ[O] FractionRing O} {n : ℕ} (e : Fin n → V)
    (f : Basis (Fin n) (FractionRing O) V') (h : ∀ i w, f.repr w i = b (e i) w) :
    dualLat b (Submodule.span O (Set.range e)) = Submodule.span O (Set.range f) := by sorry
