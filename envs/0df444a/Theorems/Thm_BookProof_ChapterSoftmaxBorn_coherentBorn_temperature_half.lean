-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxBorn_coherentBorn_temperature_half
-- name    : BookProof.ChapterSoftmaxBorn.coherentBorn_temperature_half
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T17:09:36.781758+00:00
-- url     : https://prove2.me/theorems/712b6f19-d9f0-4c3b-b2a2-c3548605b958
-- title:
--   `BookProof.ChapterSoftmaxBorn.coherentBorn_temperature_half` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r) (j : Fin m) : bornW
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxBorn`.
--
--   `BookProof.ChapterSoftmaxBorn.coherentBorn_temperature_half` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r) (j : Fin m) : bornWeight q k j = Real.exp (inner ℝ q (k j) / (1 / 2)) / ∑ l, Real.exp (inner ℝ q (k l) / (1 / 2))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxBorn.coherentBorn_temperature_half`.

-- Generated from ChapterSoftmaxBorn.lean — theorem BookProof.ChapterSoftmaxBorn.coherentBorn_temperature_half
import Definitions.Def_ChapterCoherentOverlap
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxBorn


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxBorn.coherentBorn_temperature_half (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r) (j : Fin m) :
    bornWeight q k j =
      Real.exp (inner ℝ q (k j) / (1 / 2)) / ∑ l, Real.exp (inner ℝ q (k l) / (1 / 2)) := by sorry
