-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_projOp_apply_mem
-- name    : BookProof.BrstUnboundedLeakage.projOp_apply_mem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T10:11:44.680327+00:00
-- url     : https://prove2.me/theorems/e3eaf719-4aab-4025-ace8-6ed70d103a05
-- title:
--   `BookProof.BrstUnboundedLeakage.projOp_apply_mem` (x : H) : projOp V x ∈ V
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.projOp_apply_mem` (x : H) : projOp V x ∈ V
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.projOp_apply_mem`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.projOp_apply_mem
import Definitions.Def_ChapterBrstTruncationLeakage
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
open BookProof.BrstUnboundedLeakage


open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H)
variable (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : V ≤ T.domain)

theorem BookProof.BrstUnboundedLeakage.projOp_apply_mem (x : H) : projOp V x ∈ V := by sorry
