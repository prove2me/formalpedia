-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_neighbourConstruct_one_mem
-- name    : Formalism.HermitianLatticesTheory.neighbourConstruct_one_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:03.438439+00:00
-- url     : https://prove2.me/theorems/ba21701b-a9bf-4f86-bb42-6535b74d184b
-- title:
--   Hermitian Lattices Theory: neighbour Construct one mem
-- statement:
--   The Hermitian Lattices Theory construction uses the neighbour Construct one mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/NeighbourConstruct.lean#L58-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/NeighbourConstruct.lean#L58-L76

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
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem Formalism.HermitianLatticesTheory.neighbourConstruct_one_mem (P : Ideal R) (hP0 : P ≠ ⊥) :
    (1 : K) ∈ Submodule.map (Algebra.linearMap R K) P * invIdeal (K := K) P := by sorry
