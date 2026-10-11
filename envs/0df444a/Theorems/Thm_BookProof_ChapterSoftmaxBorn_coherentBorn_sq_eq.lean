-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxBorn_coherentBorn_sq_eq
-- name    : BookProof.ChapterSoftmaxBorn.coherentBorn_sq_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:15:40.228814+00:00
-- url     : https://prove2.me/theorems/b1321bcb-3c50-4bac-b406-b2b2cb194813
-- title:
--   `BookProof.ChapterSoftmaxBorn.coherentBorn_sq_eq` (q k : EuclideanSpace ℝ (Fin n)) : bornNumer q k = Real.exp (-‖q‖ ^ 2) * Real.exp (-‖k‖ ^ 2) * Real.exp (2 * inner ℝ q k)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxBorn`.
--
--   `BookProof.ChapterSoftmaxBorn.coherentBorn_sq_eq` (q k : EuclideanSpace ℝ (Fin n)) : bornNumer q k = Real.exp (-‖q‖ ^ 2) * Real.exp (-‖k‖ ^ 2) * Real.exp (2 * inner ℝ q k)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxBorn.coherentBorn_sq_eq`.

-- Generated from ChapterSoftmaxBorn.lean — theorem BookProof.ChapterSoftmaxBorn.coherentBorn_sq_eq
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterCoherentOverlap
open BookProof.ChapterCoherentOverlap
open BookProof.ChapterSoftmaxBorn


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxBorn.coherentBorn_sq_eq (q k : EuclideanSpace ℝ (Fin n)) :
    bornNumer q k =
      Real.exp (-‖q‖ ^ 2) * Real.exp (-‖k‖ ^ 2) * Real.exp (2 * inner ℝ q k) := by sorry
