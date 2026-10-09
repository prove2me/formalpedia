-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionQKCircuit_rank_qkMatrix_le
-- name    : BookProof.ChapterAttentionQKCircuit.rank_qkMatrix_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:41:35.497289+00:00
-- url     : https://prove2.me/theorems/d50aa555-437a-4cec-ac7e-7fd4ce9eaab2
-- title:
--   `BookProof.ChapterAttentionQKCircuit.rank_qkMatrix_le` (WQ WK : Matrix (Fin d) (Fin n) ℝ) : (qkMatrix WQ WK).rank ≤ d
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionQKCircuit`.
--
--   `BookProof.ChapterAttentionQKCircuit.rank_qkMatrix_le` (WQ WK : Matrix (Fin d) (Fin n) ℝ) : (qkMatrix WQ WK).rank ≤ d
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionQKCircuit.rank_qkMatrix_le`.

-- Generated from ChapterAttentionQKCircuit.lean — theorem BookProof.ChapterAttentionQKCircuit.rank_qkMatrix_le
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionQKCircuit
open BookProof.ChapterAttentionQKCircuit


open scoped BigOperators

noncomputable section


open Matrix BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {d n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionQKCircuit.rank_qkMatrix_le (WQ WK : Matrix (Fin d) (Fin n) ℝ) : (qkMatrix WQ WK).rank ≤ d := by sorry
