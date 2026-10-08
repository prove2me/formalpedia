-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_norm_restartIter
-- name    : BookProof.BrstUnboundedLeakage.norm_restartIter
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:31:36.207985+00:00
-- url     : https://prove2.me/theorems/13c1f13f-7aa2-4b0d-a77f-64adb5d1cc5e
-- title:
--   `BookProof.BrstUnboundedLeakage.norm_restartIter` (τ : ℝ) (x : H) (n : ℕ) : ‖leakageIter (restartGen T Vs hVs) τ x n‖ = ‖x‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.norm_restartIter` (τ : ℝ) (x : H) (n : ℕ) : ‖leakageIter (restartGen T Vs hVs) τ x n‖ = ‖x‖
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.norm_restartIter`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.norm_restartIter
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Definitions.Def_ChapterBrstTruncationLeakage
import Definitions.Def_ChapterStoneResolvent
open BookProof.BrstLeakage
open BookProof.BrstUnboundedLeakage


open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H)
variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)
variable (Vs : ℕ → Submodule ℂ H) [∀ i, FiniteDimensional ℂ (Vs i)] (hVs : ∀ i, Vs i ≤ T.domain)

theorem BookProof.BrstUnboundedLeakage.norm_restartIter (τ : ℝ) (x : H) (n : ℕ) :
    ‖leakageIter (restartGen T Vs hVs) τ x n‖ = ‖x‖ := by sorry
