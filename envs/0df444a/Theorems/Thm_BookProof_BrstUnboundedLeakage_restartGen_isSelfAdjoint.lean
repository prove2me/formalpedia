-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_restartGen_isSelfAdjoint
-- name    : BookProof.BrstUnboundedLeakage.restartGen_isSelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:20:33.707296+00:00
-- url     : https://prove2.me/theorems/107e7c0b-5920-4434-a2b0-a33ff5f3013c
-- title:
--   `BookProof.BrstUnboundedLeakage.restartGen_isSelfAdjoint` (i : ℕ) : IsSelfAdjoint (restartGen T Vs hVs i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.restartGen_isSelfAdjoint` (i : ℕ) : IsSelfAdjoint (restartGen T Vs hVs i)
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.restartGen_isSelfAdjoint`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.restartGen_isSelfAdjoint
import Definitions.Def_ChapterBrstTruncationLeakage
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Definitions.Def_ChapterStoneResolvent
open BookProof.BrstUnboundedLeakage


open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H)
variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)
variable (Vs : ℕ → Submodule ℂ H) [∀ i, FiniteDimensional ℂ (Vs i)] (hVs : ∀ i, Vs i ≤ T.domain)

theorem BookProof.BrstUnboundedLeakage.restartGen_isSelfAdjoint (i : ℕ) : IsSelfAdjoint (restartGen T Vs hVs i) := by sorry
