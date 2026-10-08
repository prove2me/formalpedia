-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_projOp_eq_self_of_mem
-- name    : BookProof.BrstUnboundedLeakage.projOp_eq_self_of_mem
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:18:43.826978+00:00
-- url     : https://prove2.me/theorems/2d71b0dc-b98b-45f5-bea6-bf48edc9657c
-- title:
--   `BookProof.BrstUnboundedLeakage.projOp_eq_self_of_mem` {x : H} (hx : x ∈ V) : projOp V x = x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.projOp_eq_self_of_mem` {x : H} (hx : x ∈ V) : projOp V x = x
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.projOp_eq_self_of_mem`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.projOp_eq_self_of_mem
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

theorem BookProof.BrstUnboundedLeakage.projOp_eq_self_of_mem {x : H} (hx : x ∈ V) : projOp V x = x := by sorry
