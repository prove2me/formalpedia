-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_neighbourBasic_not_le
-- name    : Formalism.HermitianLatticesTheory.neighbourBasic_not_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:06.153411+00:00
-- url     : https://prove2.me/theorems/41898ae2-fe8f-4e6d-82c8-c638e5eefc36
-- title:
--   Hermitian Lattices Theory: neighbour Basic not le
-- statement:
--   The Hermitian Lattices Theory construction uses the neighbour Basic not le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/NeighbourBasic.lean#L66-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/NeighbourBasic.lean#L66-L76

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

theorem Formalism.HermitianLatticesTheory.neighbourBasic_not_le {I : Ideal R} (hI : I ≠ ⊤) {L N : Submodule R V}
    (e : (L ⧸ N.comap L.subtype) ≃ₗ[R] (R ⧸ I)) : ∃ l ∈ L, l ∉ N := by sorry
