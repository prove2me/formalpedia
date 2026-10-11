-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxSharpness_ampBorn_nonneg
-- name    : BookProof.ChapterSoftmaxSharpness.ampBorn_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:36:39.015971+00:00
-- url     : https://prove2.me/theorems/37b5a755-d089-4e7e-96c7-2912fc352a88
-- title:
--   `BookProof.ChapterSoftmaxSharpness.ampBorn_nonneg` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : 0 ≤ ampBorn q k j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxSharpness`.
--
--   `BookProof.ChapterSoftmaxSharpness.ampBorn_nonneg` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : 0 ≤ ampBorn q k j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxSharpness.ampBorn_nonneg`.

-- Generated from ChapterSoftmaxSharpness.lean — theorem BookProof.ChapterSoftmaxSharpness.ampBorn_nonneg
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness


open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxSharpness.ampBorn_nonneg (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n))
    (j : Fin m) : 0 ≤ ampBorn q k j := by sorry
