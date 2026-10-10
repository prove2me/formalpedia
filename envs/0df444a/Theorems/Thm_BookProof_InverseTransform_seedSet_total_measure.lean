-- Prove2me | Theorems.Thm_BookProof_InverseTransform_seedSet_total_measure
-- name    : BookProof.InverseTransform.seedSet_total_measure
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:17:44.481335+00:00
-- url     : https://prove2.me/theorems/efb3f718-11e5-4907-abff-3c5bc7d3a7fb
-- title:
--   `BookProof.InverseTransform.seedSet_total_measure` (hp : ∀ i, 0 ≤ p i) (hsum : cdf p n = 1) : ∑ k ∈ Finset.range n, volume (seedSet p k) = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterInverseTransform`.
--
--   `BookProof.InverseTransform.seedSet_total_measure` (hp : ∀ i, 0 ≤ p i) (hsum : cdf p n = 1) : ∑ k ∈ Finset.range n, volume (seedSet p k) = 1
--
--   Formalization note: Lean 4 identifier `BookProof.InverseTransform.seedSet_total_measure`.

-- Generated from ChapterInverseTransform.lean — theorem BookProof.InverseTransform.seedSet_total_measure
import Mathlib
import Definitions.Def_ChapterInverseTransform
open BookProof.InverseTransform



open MeasureTheory Set Function

variable {n : ℕ} (p : ℕ → ℝ)

theorem BookProof.InverseTransform.seedSet_total_measure (hp : ∀ i, 0 ≤ p i) (hsum : cdf p n = 1) :
    ∑ k ∈ Finset.range n, volume (seedSet p k) = 1 := by sorry
