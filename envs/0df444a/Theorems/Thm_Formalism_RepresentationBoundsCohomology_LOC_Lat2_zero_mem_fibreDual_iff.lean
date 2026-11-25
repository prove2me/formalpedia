-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_Lat2_zero_mem_fibreDual_iff
-- name    : Formalism.RepresentationBoundsCohomology.LOC.Lat2.zero_mem_fibreDual_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:52:38.552254+00:00
-- url     : https://prove2.me/theorems/0103b2c5-5986-435d-bffc-f24789ec84ad
-- title:
--   Lat2: zero mem fibre Dual iff
-- statement:
--   The Lat2 construction uses the zero mem fibre Dual iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/ExistsBasisOfLattice.lean#L209-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/ExistsBasisOfLattice.lean#L209-L221

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
open Lat2
open Formalism.RepresentationBoundsCohomology.LOC.Lat2
variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {VY VT VY' VT' : Type u}
  [AddCommGroup VY] [Module O VY] [Module (FractionRing O) VY] [IsScalarTower O (FractionRing O) VY]
  [AddCommGroup VT] [Module O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
  [AddCommGroup VY'] [Module O VY'] [AddCommGroup VT'] [Module O VT']
omit [IsDiscreteValuationRing O] [Module (FractionRing O) VY]
  [IsScalarTower O (FractionRing O) VY] [Module (FractionRing O) VT]
  [IsScalarTower O (FractionRing O) VT]

theorem Formalism.RepresentationBoundsCohomology.LOC.Lat2.zero_mem_fibreDual_iff (bY : VY →ₗ[O] VY' →ₗ[O] FractionRing O)
    (bT : VT →ₗ[O] VT' →ₗ[O] FractionRing O) (Y : Submodule O VY) (T : Submodule O VT)
    (φ : Y →ₗ[O] VT ⧸ T) (g : VY') :
    ((0 : VT'), g) ∈ fibreDual bY bT Y T φ ↔ g ∈ dualLat bY Y := by sorry
