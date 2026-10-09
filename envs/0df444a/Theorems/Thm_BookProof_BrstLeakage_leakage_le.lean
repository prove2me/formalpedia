-- Prove2me | Theorems.Thm_BookProof_BrstLeakage_leakage_le
-- name    : BookProof.BrstLeakage.leakage_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:13:13.980644+00:00
-- url     : https://prove2.me/theorems/183fd9b2-3037-4eca-b3bf-194ead46a97c
-- title:
--   `BookProof.BrstLeakage.leakage_le` {H B Om : E →L[ℂ] E} (hH : IsSelfAdjoint H) (hcomm : Commute H Om) (t : ℝ) (ht : 0 ≤ t) (x : E) (K : ℝ) (hK : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖(H - B) (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstTruncationLeakage`.
--
--   `BookProof.BrstLeakage.leakage_le` {H B Om : E →L[ℂ] E} (hH : IsSelfAdjoint H) (hcomm : Commute H Om) (t : ℝ) (ht : 0 ≤ t) (x : E) (K : ℝ) (hK : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖(H - B) (flow B s x)‖ ≤ K) : ‖Om (flow B t x)‖ ≤ ‖Om x‖ + ‖Om‖ * (K * t)
--
--   Formalization note: Lean 4 identifier `BookProof.BrstLeakage.leakage_le`.

-- Generated from ChapterBrstTruncationLeakage.lean — theorem BookProof.BrstLeakage.leakage_le
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage


open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.BrstLeakage.leakage_le {H B Om : E →L[ℂ] E} (hH : IsSelfAdjoint H) (hcomm : Commute H Om)
    (t : ℝ) (ht : 0 ≤ t) (x : E) (K : ℝ)
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖(H - B) (flow B s x)‖ ≤ K) :
    ‖Om (flow B t x)‖ ≤ ‖Om x‖ + ‖Om‖ * (K * t) := by sorry
