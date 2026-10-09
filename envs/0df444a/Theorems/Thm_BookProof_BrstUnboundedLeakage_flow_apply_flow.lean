-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_flow_apply_flow
-- name    : BookProof.BrstUnboundedLeakage.flow_apply_flow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:17:54.223222+00:00
-- url     : https://prove2.me/theorems/27445640-4293-454a-a3d8-a32712250f92
-- title:
--   `BookProof.BrstUnboundedLeakage.flow_apply_flow` (B : H →L[ℂ] H) (s u : ℝ) (x : H) : flow B u (flow B s x) = flow B (u + s) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.flow_apply_flow` (B : H →L[ℂ] H) (s u : ℝ) (x : H) : flow B u (flow B s x) = flow B (u + s) x
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.flow_apply_flow`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.flow_apply_flow
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Definitions.Def_ChapterBrstTruncationLeakage
open BookProof.BrstLeakage
open BookProof.BrstUnboundedLeakage


open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.BrstUnboundedLeakage.flow_apply_flow (B : H →L[ℂ] H) (s u : ℝ) (x : H) :
    flow B u (flow B s x) = flow B (u + s) x := by sorry
