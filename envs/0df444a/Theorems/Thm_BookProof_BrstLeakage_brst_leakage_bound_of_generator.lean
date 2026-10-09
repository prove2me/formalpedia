-- Prove2me | Theorems.Thm_BookProof_BrstLeakage_brst_leakage_bound_of_generator
-- name    : BookProof.BrstLeakage.brst_leakage_bound_of_generator
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:17:17.527234+00:00
-- url     : https://prove2.me/theorems/48a9431a-4288-4be0-8ce8-ae614cb25dac
-- title:
--   `BookProof.BrstLeakage.brst_leakage_bound_of_generator` {H B Om : E →L[ℂ] E} (hH : IsSelfAdjoint H) (hB : IsSelfAdjoint B) (hcomm : Commute H Om) (tau : ℝ) (htau : 0 ≤ tau) (n : ℕ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstTruncationLeakage`.
--
--   `BookProof.BrstLeakage.brst_leakage_bound_of_generator` {H B Om : E →L[ℂ] E} (hH : IsSelfAdjoint H) (hB : IsSelfAdjoint B) (hcomm : Commute H Om) (tau : ℝ) (htau : 0 ≤ tau) (n : ℕ) (v : E) (hv : Om v = 0) : ‖Om (((flow B tau) ^ n) v)‖ ≤ ‖Om‖ * (n * (‖H - B‖ * tau) * ‖v‖)
--
--   Formalization note: Lean 4 identifier `BookProof.BrstLeakage.brst_leakage_bound_of_generator`.

-- Generated from ChapterBrstTruncationLeakage.lean — theorem BookProof.BrstLeakage.brst_leakage_bound_of_generator
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage


open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.BrstLeakage.brst_leakage_bound_of_generator {H B Om : E →L[ℂ] E} (hH : IsSelfAdjoint H)
    (hB : IsSelfAdjoint B) (hcomm : Commute H Om) (tau : ℝ) (htau : 0 ≤ tau)
    (n : ℕ) (v : E) (hv : Om v = 0) :
    ‖Om (((flow B tau) ^ n) v)‖ ≤ ‖Om‖ * (n * (‖H - B‖ * tau) * ‖v‖) := by sorry
