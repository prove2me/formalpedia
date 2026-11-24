-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_Lat2_exists_dual_basis
-- name    : Formalism.RepresentationBoundsCohomology.LOC.Lat2.exists_dual_basis
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:27:19.228449+00:00
-- url     : https://prove2.me/theorems/f1b95f5d-782d-4761-8aa2-169571cb4a39
-- title:
--   Lat2: exists dual basis
-- statement:
--   The Lat2 construction uses the exists dual basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/ExistsBasisOfLattice.lean#L53-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/ExistsBasisOfLattice.lean#L53-L89

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

theorem Formalism.RepresentationBoundsCohomology.LOC.Lat2.exists_dual_basis {b : V →ₗ[O] V' →ₗ[O] FractionRing O} (hb : PerfectRight b) {n : ℕ}
    (e : Basis (Fin n) (FractionRing O) V) :
    ∃ f : Basis (Fin n) (FractionRing O) V',
      (∀ i x, e.repr x i = b x (f i)) ∧ (∀ i w, f.repr w i = b (e i) w) := by sorry
