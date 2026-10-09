-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionQKCircuit_qkMatrix_gauge
-- name    : BookProof.ChapterAttentionQKCircuit.qkMatrix_gauge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:40:53.738513+00:00
-- url     : https://prove2.me/theorems/45ba5118-b1f3-434d-b38c-c8a67932158e
-- title:
--   `BookProof.ChapterAttentionQKCircuit.qkMatrix_gauge` {A B : Matrix (Fin d) (Fin d) ℝ} (hAB : Aᵀ * B = 1) (WQ WK : Matrix (Fin d) (Fin n) ℝ) : qkMatrix (A * WQ) (B * WK) = qkMatrix
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionQKCircuit`.
--
--   `BookProof.ChapterAttentionQKCircuit.qkMatrix_gauge` {A B : Matrix (Fin d) (Fin d) ℝ} (hAB : Aᵀ * B = 1) (WQ WK : Matrix (Fin d) (Fin n) ℝ) : qkMatrix (A * WQ) (B * WK) = qkMatrix WQ WK
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionQKCircuit.qkMatrix_gauge`.

-- Generated from ChapterAttentionQKCircuit.lean — theorem BookProof.ChapterAttentionQKCircuit.qkMatrix_gauge
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionQKCircuit
open BookProof.ChapterAttentionQKCircuit


open scoped BigOperators

noncomputable section


open Matrix BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {d n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionQKCircuit.qkMatrix_gauge {A B : Matrix (Fin d) (Fin d) ℝ} (hAB : Aᵀ * B = 1)
    (WQ WK : Matrix (Fin d) (Fin n) ℝ) :
    qkMatrix (A * WQ) (B * WK) = qkMatrix WQ WK := by sorry
