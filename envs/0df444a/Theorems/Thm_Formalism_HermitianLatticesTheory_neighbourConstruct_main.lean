-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_neighbourConstruct_main
-- name    : Formalism.HermitianLatticesTheory.neighbourConstruct_main
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:05.590151+00:00
-- url     : https://prove2.me/theorems/831d6c81-63bd-4cbc-8c14-13e04b408ec2
-- title:
--   Hermitian Lattices Theory: neighbour Construct main
-- statement:
--   The Hermitian Lattices Theory construction uses the neighbour Construct main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/NeighbourConstruct.lean#L117-L421
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/NeighbourConstruct.lean#L117-L421

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
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem Formalism.HermitianLatticesTheory.neighbourConstruct_main (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (P : Ideal R) (hP : P.IsMaximal) (hP0 : P ≠ ⊥) (L : Submodule R V)
    (hLat : Submodule.IsLattice K L) (hL : IsUnimodular h L) (x : V) (hx : x ∈ L)
    (hxP : x ∉ P • L) (hxx : ∃ r ∈ P * conjIdeal (K := K) P, algebraMap R K r = h x x) :
      Submodule.IsLattice K (neighbourOf h P L x) ∧
      IsIntegralLat h (neighbourOf h P L x) ∧ IsUnimodular h (neighbourOf h P L x) ∧
      IsNeighbour (K := K) P L (neighbourOf h P L x) ∧
      L ⊓ neighbourOf h P L x = neighbourCore h P L x := by sorry
