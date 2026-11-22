-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_neighbourConstruct_mem_inv
-- name    : Formalism.HermitianLatticesTheory.neighbourConstruct_mem_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:23:32.64609+00:00
-- url     : https://prove2.me/theorems/e3e6c15c-a925-4499-8263-cd8b57d92231
-- title:
--   Hermitian Lattices Theory: neighbour Construct mem inv
-- statement:
--   The Hermitian Lattices Theory construction uses the neighbour Construct mem inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/NeighbourConstruct.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/NeighbourConstruct.lean#L18-L22

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

theorem Formalism.HermitianLatticesTheory.neighbourConstruct_mem_inv {P : Ideal R} {a : K} :
    a ∈ invIdeal (K := K) P ↔ ∀ p ∈ P, algebraMap R K p * a ∈ Set.range (algebraMap R K) := by sorry
