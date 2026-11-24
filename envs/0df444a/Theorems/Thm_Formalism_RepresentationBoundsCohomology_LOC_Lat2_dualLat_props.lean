-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_Lat2_dualLat_props
-- name    : Formalism.RepresentationBoundsCohomology.LOC.Lat2.dualLat_props
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:27:05.779605+00:00
-- url     : https://prove2.me/theorems/cc831134-f05a-4de9-8ca4-3f9cf24e3165
-- title:
--   Lat2: dual Lat props
-- statement:
--   The Lat2 construction uses the dual Lat props property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/ExistsBasisOfLattice.lean#L112-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/ExistsBasisOfLattice.lean#L112-L123

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

theorem Formalism.RepresentationBoundsCohomology.LOC.Lat2.dualLat_props {b : V →ₗ[O] V' →ₗ[O] FractionRing O} {T : Submodule O V}
    (hT : IsLatticeIn T) (hb : PerfectRight b) :
    IsLatticeIn (dualLat b T) ∧ finrank O (dualLat b T) = finrank O T ∧
      dualLat b.flip (dualLat b T) = T := by sorry
