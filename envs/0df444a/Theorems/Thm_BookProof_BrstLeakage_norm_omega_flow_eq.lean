-- Prove2me | Theorems.Thm_BookProof_BrstLeakage_norm_omega_flow_eq
-- name    : BookProof.BrstLeakage.norm_omega_flow_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:30:28.269976+00:00
-- url     : https://prove2.me/theorems/1c4b9bdf-2adb-42ac-ad6d-582d61a95892
-- title:
--   `BookProof.BrstLeakage.norm_omega_flow_eq` {A Om : E →L[ℂ] E} (hA : IsSelfAdjoint A) (h : Commute A Om) (t : ℝ) (x : E) : ‖Om (flow A t x)‖ = ‖Om x‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstTruncationLeakage`.
--
--   `BookProof.BrstLeakage.norm_omega_flow_eq` {A Om : E →L[ℂ] E} (hA : IsSelfAdjoint A) (h : Commute A Om) (t : ℝ) (x : E) : ‖Om (flow A t x)‖ = ‖Om x‖
--
--   Formalization note: Lean 4 identifier `BookProof.BrstLeakage.norm_omega_flow_eq`.

-- Generated from ChapterBrstTruncationLeakage.lean — theorem BookProof.BrstLeakage.norm_omega_flow_eq
import Mathlib
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage


open NormedSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.BrstLeakage.norm_omega_flow_eq {A Om : E →L[ℂ] E} (hA : IsSelfAdjoint A) (h : Commute A Om)
    (t : ℝ) (x : E) : ‖Om (flow A t x)‖ = ‖Om x‖ := by sorry
