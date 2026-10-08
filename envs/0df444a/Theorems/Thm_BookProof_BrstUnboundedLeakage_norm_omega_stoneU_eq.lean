-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_norm_omega_stoneU_eq
-- name    : BookProof.BrstUnboundedLeakage.norm_omega_stoneU_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:30:48.349003+00:00
-- url     : https://prove2.me/theorems/2459b4ea-bf0c-47a1-a90e-2abed39c689a
-- title:
--   `BookProof.BrstUnboundedLeakage.norm_omega_stoneU_eq` {Om : H →L[ℂ] H} (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y)) (t : ℝ) (x : H) : ‖Om (T.stoneU t x)‖ = ‖O
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.norm_omega_stoneU_eq` {Om : H →L[ℂ] H} (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y)) (t : ℝ) (x : H) : ‖Om (T.stoneU t x)‖ = ‖Om x‖
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.norm_omega_stoneU_eq`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.norm_omega_stoneU_eq
import Definitions.Def_ChapterBrstTruncationLeakage
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
open BookProof.BrstUnboundedLeakage


open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H)

theorem BookProof.BrstUnboundedLeakage.norm_omega_stoneU_eq {Om : H →L[ℂ] H}
    (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y)) (t : ℝ) (x : H) :
    ‖Om (T.stoneU t x)‖ = ‖Om x‖ := by sorry
