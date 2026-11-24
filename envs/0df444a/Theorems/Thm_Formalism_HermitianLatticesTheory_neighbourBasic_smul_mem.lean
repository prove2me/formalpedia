-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_neighbourBasic_smul_mem
-- name    : Formalism.HermitianLatticesTheory.neighbourBasic_smul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:17.123814+00:00
-- url     : https://prove2.me/theorems/d72e1a31-1181-4069-b55b-2775017d624f
-- title:
--   Hermitian Lattices Theory: neighbour Basic smul mem
-- statement:
--   The Hermitian Lattices Theory construction uses the neighbour Basic smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/NeighbourBasic.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/NeighbourBasic.lean#L14-L23

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem Formalism.HermitianLatticesTheory.neighbourBasic_smul_mem {I : Ideal R} {L N : Submodule R V}
    (e : (L ⧸ N.comap L.subtype) ≃ₗ[R] (R ⧸ I)) {r : R} (hr : r ∈ I) {l : V} (hl : l ∈ L) :
    r • l ∈ N := by sorry
