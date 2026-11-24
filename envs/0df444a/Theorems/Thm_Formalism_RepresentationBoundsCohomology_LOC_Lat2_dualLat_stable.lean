-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_Lat2_dualLat_stable
-- name    : Formalism.RepresentationBoundsCohomology.LOC.Lat2.dualLat_stable
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:26:29.881402+00:00
-- url     : https://prove2.me/theorems/bdbe392e-9d1d-4473-b9c3-f7e60a0b9142
-- title:
--   Lat2: dual Lat stable
-- statement:
--   The Lat2 construction uses the dual Lat stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/ExistsBasisOfLattice.lean#L128-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/ExistsBasisOfLattice.lean#L128-L135

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
  [Module (FractionRing O) V'] [IsScalarTower O (FractionRing O) V']

theorem Formalism.RepresentationBoundsCohomology.LOC.Lat2.dualLat_stable {G : Type u} [Group G] {ε : G →* Oˣ} {ρ : Representation O G V}
    {ρ' : Representation O G V'} {b : V →ₗ[O] V' →ₗ[O] FractionRing O} {T : Submodule O V}
    (hs : StableUnder ρ T) (he : EquivPair ε ρ ρ' b) : StableUnder ρ' (dualLat b T) := by sorry
