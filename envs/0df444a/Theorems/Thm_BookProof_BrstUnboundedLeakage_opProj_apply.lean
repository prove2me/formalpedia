-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_opProj_apply
-- name    : BookProof.BrstUnboundedLeakage.opProj_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:19:21.881386+00:00
-- url     : https://prove2.me/theorems/e552d00b-533c-478c-a103-ed9ceb2e8578
-- title:
--   `BookProof.BrstUnboundedLeakage.opProj_apply` (x : H) : opProj T V hV x = T.op ⟨projOp V x, hV (projOp_apply_mem V x)⟩
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.opProj_apply` (x : H) : opProj T V hV x = T.op ⟨projOp V x, hV (projOp_apply_mem V x)⟩
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.opProj_apply`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.opProj_apply
import Definitions.Def_ChapterBrstTruncationLeakage
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Definitions.Def_ChapterStoneResolvent
import Theorems.Thm_BookProof_BrstUnboundedLeakage_projOp_apply_mem
open BookProof.BrstUnboundedLeakage


open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H)
variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)

theorem BookProof.BrstUnboundedLeakage.opProj_apply (x : H) : opProj T V hV x = T.op ⟨projOp V x, hV (projOp_apply_mem V x)⟩ := by sorry
