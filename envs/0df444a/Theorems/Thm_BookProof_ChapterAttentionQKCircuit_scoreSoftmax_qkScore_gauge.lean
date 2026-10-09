-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionQKCircuit_scoreSoftmax_qkScore_gauge
-- name    : BookProof.ChapterAttentionQKCircuit.scoreSoftmax_qkScore_gauge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:41:16.535687+00:00
-- url     : https://prove2.me/theorems/e14c075f-f13c-4a2e-a652-6380f57419c7
-- title:
--   `BookProof.ChapterAttentionQKCircuit.scoreSoftmax_qkScore_gauge` (beta : ℝ) {A B : Matrix (Fin d) (Fin d) ℝ} (hAB : Aᵀ * B = 1) (WQ WK : Matrix (Fin d) (Fin n) ℝ) (x : Fin n → ℝ) (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionQKCircuit`.
--
--   `BookProof.ChapterAttentionQKCircuit.scoreSoftmax_qkScore_gauge` (beta : ℝ) {A B : Matrix (Fin d) (Fin d) ℝ} (hAB : Aᵀ * B = 1) (WQ WK : Matrix (Fin d) (Fin n) ℝ) (x : Fin n → ℝ) (k : Fin m → Fin n → ℝ) (j : Fin m) : scoreSoftmax beta (fun l => qkScore (A * WQ) (B * WK) x (k l)) j = scoreSoftmax beta (fun l => qkScore WQ WK x (k l)) j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionQKCircuit.scoreSoftmax_qkScore_gauge`.

-- Generated from ChapterAttentionQKCircuit.lean — theorem BookProof.ChapterAttentionQKCircuit.scoreSoftmax_qkScore_gauge
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionQKCircuit
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionQKCircuit


open scoped BigOperators

noncomputable section


open Matrix BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {d n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionQKCircuit.scoreSoftmax_qkScore_gauge (beta : ℝ) {A B : Matrix (Fin d) (Fin d) ℝ}
    (hAB : Aᵀ * B = 1) (WQ WK : Matrix (Fin d) (Fin n) ℝ) (x : Fin n → ℝ)
    (k : Fin m → Fin n → ℝ) (j : Fin m) :
    scoreSoftmax beta (fun l => qkScore (A * WQ) (B * WK) x (k l)) j
      = scoreSoftmax beta (fun l => qkScore WQ WK x (k l)) j := by sorry
