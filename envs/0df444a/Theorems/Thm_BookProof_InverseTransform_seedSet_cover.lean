-- Prove2me | Theorems.Thm_BookProof_InverseTransform_seedSet_cover
-- name    : BookProof.InverseTransform.seedSet_cover
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:17:27.238246+00:00
-- url     : https://prove2.me/theorems/449b1bc6-cf05-4c65-bacf-e72629212f24
-- title:
--   `BookProof.InverseTransform.seedSet_cover` (hp : ∀ i, 0 ≤ p i) (hsum : cdf p n = 1) : (⋃ k ∈ Finset.range n, seedSet p k) = Set.Ico (0 : ℝ) 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterInverseTransform`.
--
--   `BookProof.InverseTransform.seedSet_cover` (hp : ∀ i, 0 ≤ p i) (hsum : cdf p n = 1) : (⋃ k ∈ Finset.range n, seedSet p k) = Set.Ico (0 : ℝ) 1
--
--   Formalization note: Lean 4 identifier `BookProof.InverseTransform.seedSet_cover`.

-- Generated from ChapterInverseTransform.lean — theorem BookProof.InverseTransform.seedSet_cover
import Mathlib
import Definitions.Def_ChapterInverseTransform
open BookProof.InverseTransform



open MeasureTheory Set Function

variable {n : ℕ} (p : ℕ → ℝ)

theorem BookProof.InverseTransform.seedSet_cover (hp : ∀ i, 0 ≤ p i) (hsum : cdf p n = 1) :
    (⋃ k ∈ Finset.range n, seedSet p k) = Set.Ico (0 : ℝ) 1 := by sorry
