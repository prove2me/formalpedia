-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_neighbourConstruct_avoid
-- name    : Formalism.HermitianLatticesTheory.neighbourConstruct_avoid
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:14.539537+00:00
-- url     : https://prove2.me/theorems/61733c11-f68a-41dd-931f-5801d83fd656
-- title:
--   Hermitian Lattices Theory: neighbour Construct avoid
-- statement:
--   The Hermitian Lattices Theory construction uses the neighbour Construct avoid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/NeighbourConstruct.lean#L97-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/NeighbourConstruct.lean#L97-L108

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
variable {R : Type*} [CommRing R]

theorem Formalism.HermitianLatticesTheory.neighbourConstruct_avoid {A B C : Ideal R} (hA : A.IsMaximal) (hB : B.IsMaximal)
    (hC : C.IsMaximal) (hAB : A ≠ B) (hAC : A ≠ C) : ∃ s ∈ A, s ∉ B ∧ s ∉ C := by sorry
