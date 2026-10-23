-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_restart_leakage_le
-- name    : BookProof.BrstUnboundedLeakage.restart_leakage_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-22T16:59:35.239104+00:00
-- url     : https://prove2.me/theorems/a787b7cc-4a59-4d0f-b425-892ba0c5adcd
-- title:
--   `BookProof.BrstUnboundedLeakage.restart_leakage_le` {Om : H →L[ℂ] H} (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y)) (τ : ℝ) (hτ : 0 ≤ τ) (x : H) (D : ℝ) (hret :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.restart_leakage_le` {Om : H →L[ℂ] H} (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y)) (τ : ℝ) (hτ : 0 ≤ τ) (x : H) (D : ℝ) (hret : ∀ i, leakageIter (restartGen T Vs hVs) τ x i ∈ Vs i) (hD : ∀ i, ‖truncDefect T (Vs i) (hVs i)‖ ≤ D) : ∀ n : ℕ, ‖Om (leakageIter (restartGen T Vs hVs) τ x n)‖ ≤ ‖Om x‖ + n * (‖Om‖ * (D * ‖x‖ * τ)) | 0 => by simp | n + 1 => by have hxn : ‖leakageIter (restartGen T Vs hVs) τ x n‖ = ‖x‖
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.restart_leakage_le`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.restart_leakage_le
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Definitions.Def_ChapterBrstTruncationLeakage
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterBrstTruncationLeakage
import Definitions.Def_ChapterBrstUnboundedLeakage
open BookProof.BrstLeakage
open BookProof.BrstUnboundedLeakage


open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H)
variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)
variable (Vs : ℕ → Submodule ℂ H) [∀ i, FiniteDimensional ℂ (Vs i)] (hVs : ∀ i, Vs i ≤ T.domain)

theorem BookProof.BrstUnboundedLeakage.restart_leakage_le {Om : H →L[ℂ] H}
    (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y))
    (τ : ℝ) (hτ : 0 ≤ τ) (x : H) (D : ℝ)
    (hret : ∀ i, leakageIter (restartGen T Vs hVs) τ x i ∈ Vs i)
    (hD : ∀ i, ‖truncDefect T (Vs i) (hVs i)‖ ≤ D) :
    ∀ n : ℕ, ‖Om (leakageIter (restartGen T Vs hVs) τ x n)‖
      ≤ ‖Om x‖ + n * (‖Om‖ * (D * ‖x‖ * τ)) := by sorry
