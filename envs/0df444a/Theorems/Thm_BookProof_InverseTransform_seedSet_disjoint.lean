-- Prove2me | Theorems.Thm_BookProof_InverseTransform_seedSet_disjoint
-- name    : BookProof.InverseTransform.seedSet_disjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:17:04.72616+00:00
-- url     : https://prove2.me/theorems/c8b2edd4-62d0-4d1c-988c-fce623030cd6
-- title:
--   `BookProof.InverseTransform.seedSet_disjoint` (hp : ∀ i, 0 ≤ p i) : Pairwise (Disjoint on seedSet p)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterInverseTransform`.
--
--   `BookProof.InverseTransform.seedSet_disjoint` (hp : ∀ i, 0 ≤ p i) : Pairwise (Disjoint on seedSet p)
--
--   Formalization note: Lean 4 identifier `BookProof.InverseTransform.seedSet_disjoint`.

-- Generated from ChapterInverseTransform.lean — theorem BookProof.InverseTransform.seedSet_disjoint
import Mathlib
import Definitions.Def_ChapterInverseTransform
open BookProof.InverseTransform



open MeasureTheory Set Function

variable {n : ℕ} (p : ℕ → ℝ)

theorem BookProof.InverseTransform.seedSet_disjoint (hp : ∀ i, 0 ≤ p i) :
    Pairwise (Disjoint on seedSet p) := by sorry
