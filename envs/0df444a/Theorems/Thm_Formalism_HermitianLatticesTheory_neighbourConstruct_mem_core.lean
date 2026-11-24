-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_neighbourConstruct_mem_core
-- name    : Formalism.HermitianLatticesTheory.neighbourConstruct_mem_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:14.039282+00:00
-- url     : https://prove2.me/theorems/64e8cdab-ed58-43ad-a62b-e31bf3ade921
-- title:
--   Hermitian Lattices Theory: neighbour Construct mem core
-- statement:
--   The Hermitian Lattices Theory construction uses the neighbour Construct mem core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/NeighbourConstruct.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/NeighbourConstruct.lean#L43-L48

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_NeighbourConstruct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourConstruct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open nonZeroDivisors
open Formalism Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem Formalism.HermitianLatticesTheory.neighbourConstruct_mem_core (h : V →ₗ⋆[K] V →ₗ[K] K) (P : Ideal R) (L : Submodule R V)
    (x y : V) : y ∈ neighbourCore h P L x ↔
      y ∈ L ∧ ∃ t ∈ conjIdeal (K := K) P, algebraMap R K t = h x y := by sorry
