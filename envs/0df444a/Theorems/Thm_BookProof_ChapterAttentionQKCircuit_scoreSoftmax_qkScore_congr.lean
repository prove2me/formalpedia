-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionQKCircuit_scoreSoftmax_qkScore_congr
-- name    : BookProof.ChapterAttentionQKCircuit.scoreSoftmax_qkScore_congr
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:43:04.952143+00:00
-- url     : https://prove2.me/theorems/7777aef4-b773-4407-8e3b-9b78a3c15128
-- title:
--   `BookProof.ChapterAttentionQKCircuit.scoreSoftmax_qkScore_congr` (beta : ℝ) {WQ₁ WK₁ WQ₂ WK₂ : Matrix (Fin d) (Fin n) ℝ} (h : qkMatrix WQ₁ WK₁ = qkMatrix WQ₂ WK₂) (x : Fin n...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionQKCircuit`.
--
--   `BookProof.ChapterAttentionQKCircuit.scoreSoftmax_qkScore_congr` (beta : ℝ) {WQ₁ WK₁ WQ₂ WK₂ : Matrix (Fin d) (Fin n) ℝ} (h : qkMatrix WQ₁ WK₁ = qkMatrix WQ₂ WK₂) (x : Fin n → ℝ) (k : Fin m → Fin n → ℝ) (j : Fin m) : scoreSoftmax beta (fun l => qkScore WQ₁ WK₁ x (k l)) j = scoreSoftmax beta (fun l => qkScore WQ₂ WK₂ x (k l)) j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionQKCircuit.scoreSoftmax_qkScore_congr`.

-- Generated from ChapterAttentionQKCircuit.lean — theorem BookProof.ChapterAttentionQKCircuit.scoreSoftmax_qkScore_congr
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

theorem BookProof.ChapterAttentionQKCircuit.scoreSoftmax_qkScore_congr (beta : ℝ) {WQ₁ WK₁ WQ₂ WK₂ : Matrix (Fin d) (Fin n) ℝ}
    (h : qkMatrix WQ₁ WK₁ = qkMatrix WQ₂ WK₂) (x : Fin n → ℝ) (k : Fin m → Fin n → ℝ)
    (j : Fin m) :
    scoreSoftmax beta (fun l => qkScore WQ₁ WK₁ x (k l)) j
      = scoreSoftmax beta (fun l => qkScore WQ₂ WK₂ x (k l)) j := by sorry
