-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_bornWeightC_phase_invariant
-- name    : BookProof.ChapterCoherentOverlapComplex.bornWeightC_phase_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:03:22.139733+00:00
-- url     : https://prove2.me/theorems/94174f71-b537-452c-9e98-db119a571a07
-- title:
--   `BookProof.ChapterCoherentOverlapComplex.bornWeightC_phase_invariant` (q : EuclideanSpace ℂ (Fin n)) (k k' : Fin m → EuclideanSpace ℂ (Fin n)) (hnorm : ∀ l, ‖k' l‖ = ‖k l‖) (hre :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOverlapComplex`.
--
--   `BookProof.ChapterCoherentOverlapComplex.bornWeightC_phase_invariant` (q : EuclideanSpace ℂ (Fin n)) (k k' : Fin m → EuclideanSpace ℂ (Fin n)) (hnorm : ∀ l, ‖k' l‖ = ‖k l‖) (hre : ∀ l, (inner ℂ q (k' l) : ℂ).re = (inner ℂ q (k l) : ℂ).re) (j : Fin m) : bornWeightC q k' j = bornWeightC q k j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOverlapComplex.bornWeightC_phase_invariant`.

-- Generated from ChapterCoherentOverlapComplex.lean — theorem BookProof.ChapterCoherentOverlapComplex.bornWeightC_phase_invariant
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentOverlapComplex


open scoped BigOperators

noncomputable section


variable {n m : ℕ}

theorem BookProof.ChapterCoherentOverlapComplex.bornWeightC_phase_invariant (q : EuclideanSpace ℂ (Fin n))
    (k k' : Fin m → EuclideanSpace ℂ (Fin n)) (hnorm : ∀ l, ‖k' l‖ = ‖k l‖)
    (hre : ∀ l, (inner ℂ q (k' l) : ℂ).re = (inner ℂ q (k l) : ℂ).re) (j : Fin m) :
    bornWeightC q k' j = bornWeightC q k j := by sorry
