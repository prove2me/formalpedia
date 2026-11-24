-- Prove2me | Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_Lat2_finrank_span_basis
-- name    : Formalism.RepresentationBoundsCohomology.LOC.Lat2.finrank_span_basis
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:26:14.058799+00:00
-- url     : https://prove2.me/theorems/8e371a65-62c9-482c-8263-210b20e4842e
-- title:
--   Lat2: finrank span basis
-- statement:
--   The Lat2 construction uses the finrank span basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/ExistsBasisOfLattice.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/LatticeDualFibres/LatticeDualProofs/ExistsBasisOfLattice.lean#L47-L51

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

theorem Formalism.RepresentationBoundsCohomology.LOC.Lat2.finrank_span_basis {n : ℕ} (e : Basis (Fin n) (FractionRing O) V) :
    finrank O (Submodule.span O (Set.range e)) = n := by sorry
