-- Prove2me | Theorems.Thm_BookProof_BrstLeakage_leakage_le_abs
-- name    : BookProof.BrstLeakage.leakage_le_abs
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:14:34.810985+00:00
-- url     : https://prove2.me/theorems/16c1077b-7b79-40a7-a95b-fcff4b088243
-- title:
--   `BookProof.BrstLeakage.leakage_le_abs` {H B Om : E →L[ℂ] E} (hH : IsSelfAdjoint H) (hcomm : Commute H Om) (t : ℝ) (x : E) (K : ℝ) (hK : ∀ s : ℝ, ‖(H - B) (flow B s x)‖ ≤ K) : ‖Om (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstTruncationLeakage`.
--
--   `BookProof.BrstLeakage.leakage_le_abs` {H B Om : E →L[ℂ] E} (hH : IsSelfAdjoint H) (hcomm : Commute H Om) (t : ℝ) (x : E) (K : ℝ) (hK : ∀ s : ℝ, ‖(H - B) (flow B s x)‖ ≤ K) : ‖Om (flow B t x)‖ ≤ ‖Om x‖ + ‖Om‖ * (K * |t|)
--
--   Formalization note: Lean 4 identifier `BookProof.BrstLeakage.leakage_le_abs`.

-- Generated from ChapterBrstTruncationLeakage.lean — theorem BookProof.BrstLeakage.leakage_le_abs
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage


open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.BrstLeakage.leakage_le_abs {H B Om : E →L[ℂ] E} (hH : IsSelfAdjoint H) (hcomm : Commute H Om)
    (t : ℝ) (x : E) (K : ℝ) (hK : ∀ s : ℝ, ‖(H - B) (flow B s x)‖ ≤ K) :
    ‖Om (flow B t x)‖ ≤ ‖Om x‖ + ‖Om‖ * (K * |t|) := by sorry
