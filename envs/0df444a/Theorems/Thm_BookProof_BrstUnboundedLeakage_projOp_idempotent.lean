-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_projOp_idempotent
-- name    : BookProof.BrstUnboundedLeakage.projOp_idempotent
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:19:07.452974+00:00
-- url     : https://prove2.me/theorems/770af339-c8b1-4954-9617-351866c0ef50
-- title:
--   `BookProof.BrstUnboundedLeakage.projOp_idempotent` : IsIdempotentElem (projOp V)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.projOp_idempotent` : IsIdempotentElem (projOp V)
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.projOp_idempotent`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.projOp_idempotent
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

theorem BookProof.BrstUnboundedLeakage.projOp_idempotent : IsIdempotentElem (projOp V) := by sorry
