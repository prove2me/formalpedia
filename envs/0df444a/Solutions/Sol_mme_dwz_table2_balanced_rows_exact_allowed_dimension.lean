-- Prove2me | solution 1 for mme_dwz_table2_balanced_rows_exact_allowed_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T08:46:31.601146+00:00
-- url     : https://prove2.me/submissions/c27ebfe0-09c0-453d-b75a-ed2ee399c258

import Definitions.Def_mme_dwz_component_word_projection
import Theorems.Thm_mme_power_basisZAllowedSubtensor_restrict_MM_oneOne_of_exact_router
import Theorems.Thm_mme_power_basisZAllowedSubtensor_restrict_MM_first_of_exact_router

open MME PiTensorProduct Module
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

/-- The four balanced rectangular Table-2 rows restrict to a single MM tensor
whose nontrivial dimension is exactly the number of literal available
canonical Z words. -/
theorem solution
    {K : Type u} [Field K]
    (h013 :
      ∃ maps : ∀ s : Fin 3,
          (cwSquareCanonicalGrading K 6).classOf s
              (cwSquareBlockType 0 1 3 s) →ₗ[K]
            (MMObj K 1 1 12).V s,
        PiTensorProduct.map maps
            ((cwSquareCanonicalGrading K 6).blockTensor
              (cwSquareBlockType 0 1 3)) = MMTensor K 1 1 12 ∧
        ∃ coord : LiftedCoarsePair.{u} 6 3 ↪ Fin 12,
          ∀ p, maps 2
              (((coarseClassBasis (K := K) 6 2 3).reindex
                Equiv.ulift.symm) p) =
            (Pi.single (coord p, (0 : Fin 1)) 1 : Fin 12 × Fin 1 → K))
    (h031 :
      ∃ maps : ∀ s : Fin 3,
          (cwSquareCanonicalGrading K 6).classOf s
              (cwSquareBlockType 0 3 1 s) →ₗ[K]
            (MMObj K 1 1 12).V s,
        PiTensorProduct.map maps
            ((cwSquareCanonicalGrading K 6).blockTensor
              (cwSquareBlockType 0 3 1)) = MMTensor K 1 1 12 ∧
        ∃ coord : LiftedCoarsePair.{u} 6 1 ↪ Fin 12,
          ∀ p, maps 2
              (((coarseClassBasis (K := K) 6 2 1).reindex
                Equiv.ulift.symm) p) =
            (Pi.single (coord p, (0 : Fin 1)) 1 : Fin 12 × Fin 1 → K))
    (h103 :
      ∃ maps : ∀ s : Fin 3,
          (cwSquareCanonicalGrading K 6).classOf s
              (cwSquareBlockType 1 0 3 s) →ₗ[K]
            (MMObj K 12 1 1).V s,
        PiTensorProduct.map maps
            ((cwSquareCanonicalGrading K 6).blockTensor
              (cwSquareBlockType 1 0 3)) = MMTensor K 12 1 1 ∧
        ∃ coord : LiftedCoarsePair.{u} 6 3 ↪ Fin 12,
          ∀ p, maps 2
              (((coarseClassBasis (K := K) 6 2 3).reindex
                Equiv.ulift.symm) p) =
            (Pi.single ((0 : Fin 1), coord p) 1 : Fin 1 × Fin 12 → K))
    (h301 :
      ∃ maps : ∀ s : Fin 3,
          (cwSquareCanonicalGrading K 6).classOf s
              (cwSquareBlockType 3 0 1 s) →ₗ[K]
            (MMObj K 12 1 1).V s,
        PiTensorProduct.map maps
            ((cwSquareCanonicalGrading K 6).blockTensor
              (cwSquareBlockType 3 0 1)) = MMTensor K 12 1 1 ∧
        ∃ coord : LiftedCoarsePair.{u} 6 1 ↪ Fin 12,
          ∀ p, maps 2
              (((coarseClassBasis (K := K) 6 2 1).reindex
                Equiv.ulift.symm) p) =
            (Pi.single ((0 : Fin 1), coord p) 1 : Fin 1 × Fin 12 → K)) :
    ∀ (m : ℕ) (s : Fin 15), (s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 7) →
      let D := Nat.card
        {w : PowIndex (LiftedCoarsePair.{u} 6 (MME.DWZSquare.shapeZ s))
            (MME.DWZTable2Counts.component s * m) //
          componentWordAllowed s m w}
      ∃ a b c : ℕ,
        TensorObj.Restrict (MMObj K a b c) (restrictedComponentPower K s m) ∧
        a * b * c = D := by
  intro m s hs
  rcases hs with rfl | rfl | rfl | rfl
  · let : DecidablePred (componentWordAllowed (3 : Fin 15) m) :=
      Classical.decPred _
    rcases h013 with ⟨maps, hmaps, coord, hcoord⟩
    have hrestrict := mme_power_basisZAllowedSubtensor_restrict_MM_oneOne_of_exact_router
      (T := canonicalComponentBlock K (3 : Fin 15))
      (bZ := canonicalComponentZBasis K (3 : Fin 15))
      (MME.DWZTable2Counts.component 3 * m)
      (componentWordAllowed (3 : Fin 15) m) coord maps hmaps hcoord
    refine ⟨1, 1,
      Nat.card {w : PowIndex (LiftedCoarsePair.{u} 6
          (MME.DWZSquare.shapeZ (3 : Fin 15)))
          (MME.DWZTable2Counts.component 3 * m) //
        componentWordAllowed (3 : Fin 15) m w}, ?_, by
          simp only [Nat.one_mul]⟩
    exact hrestrict
  · let : DecidablePred (componentWordAllowed (4 : Fin 15) m) :=
      Classical.decPred _
    rcases h031 with ⟨maps, hmaps, coord, hcoord⟩
    have hrestrict := mme_power_basisZAllowedSubtensor_restrict_MM_oneOne_of_exact_router
      (T := canonicalComponentBlock K (4 : Fin 15))
      (bZ := canonicalComponentZBasis K (4 : Fin 15))
      (MME.DWZTable2Counts.component 4 * m)
      (componentWordAllowed (4 : Fin 15) m) coord maps hmaps hcoord
    refine ⟨1, 1,
      Nat.card {w : PowIndex (LiftedCoarsePair.{u} 6
          (MME.DWZSquare.shapeZ (4 : Fin 15)))
          (MME.DWZTable2Counts.component 4 * m) //
        componentWordAllowed (4 : Fin 15) m w}, ?_, by
          simp only [Nat.one_mul]⟩
    exact hrestrict
  · let : DecidablePred (componentWordAllowed (5 : Fin 15) m) :=
      Classical.decPred _
    rcases h103 with ⟨maps, hmaps, coord, hcoord⟩
    have hrestrict := mme_power_basisZAllowedSubtensor_restrict_MM_first_of_exact_router
      (T := canonicalComponentBlock K (5 : Fin 15))
      (bZ := canonicalComponentZBasis K (5 : Fin 15))
      (MME.DWZTable2Counts.component 5 * m)
      (componentWordAllowed (5 : Fin 15) m) coord maps hmaps hcoord
    refine ⟨Nat.card {w : PowIndex (LiftedCoarsePair.{u} 6
          (MME.DWZSquare.shapeZ (5 : Fin 15)))
          (MME.DWZTable2Counts.component 5 * m) //
        componentWordAllowed (5 : Fin 15) m w}, 1, 1, ?_, by
          simp only [Nat.mul_one]⟩
    exact hrestrict
  · let : DecidablePred (componentWordAllowed (7 : Fin 15) m) :=
      Classical.decPred _
    rcases h301 with ⟨maps, hmaps, coord, hcoord⟩
    have hrestrict := mme_power_basisZAllowedSubtensor_restrict_MM_first_of_exact_router
      (T := canonicalComponentBlock K (7 : Fin 15))
      (bZ := canonicalComponentZBasis K (7 : Fin 15))
      (MME.DWZTable2Counts.component 7 * m)
      (componentWordAllowed (7 : Fin 15) m) coord maps hmaps hcoord
    refine ⟨Nat.card {w : PowIndex (LiftedCoarsePair.{u} 6
          (MME.DWZSquare.shapeZ (7 : Fin 15)))
          (MME.DWZTable2Counts.component 7 * m) //
        componentWordAllowed (7 : Fin 15) m w}, 1, 1, ?_, by
          simp only [Nat.mul_one]⟩
    exact hrestrict
