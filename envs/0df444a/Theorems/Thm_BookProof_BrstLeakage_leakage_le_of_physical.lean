-- Prove2me | Theorems.Thm_BookProof_BrstLeakage_leakage_le_of_physical
-- name    : BookProof.BrstLeakage.leakage_le_of_physical
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:13:18.122268+00:00
-- url     : https://prove2.me/theorems/5142a656-d50d-4076-a35f-8ae2ef5b4496
-- title:
--   `BookProof.BrstLeakage.leakage_le_of_physical` {H B Om : E →L[ℂ] E} (hH : IsSelfAdjoint H) (hcomm : Commute H Om) (t : ℝ) (ht : 0 ≤ t) {x : E} (hx : Om x = 0) (K : ℝ) (hK : ∀ s ∈ S
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstTruncationLeakage`.
--
--   `BookProof.BrstLeakage.leakage_le_of_physical` {H B Om : E →L[ℂ] E} (hH : IsSelfAdjoint H) (hcomm : Commute H Om) (t : ℝ) (ht : 0 ≤ t) {x : E} (hx : Om x = 0) (K : ℝ) (hK : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖(H - B) (flow B s x)‖ ≤ K) : ‖Om (flow B t x)‖ ≤ ‖Om‖ * (K * t)
--
--   Formalization note: Lean 4 identifier `BookProof.BrstLeakage.leakage_le_of_physical`.

-- Generated from ChapterBrstTruncationLeakage.lean — theorem BookProof.BrstLeakage.leakage_le_of_physical
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage


open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.BrstLeakage.leakage_le_of_physical {H B Om : E →L[ℂ] E} (hH : IsSelfAdjoint H)
    (hcomm : Commute H Om) (t : ℝ) (ht : 0 ≤ t) {x : E} (hx : Om x = 0) (K : ℝ)
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖(H - B) (flow B s x)‖ ≤ K) :
    ‖Om (flow B t x)‖ ≤ ‖Om‖ * (K * t) := by sorry
