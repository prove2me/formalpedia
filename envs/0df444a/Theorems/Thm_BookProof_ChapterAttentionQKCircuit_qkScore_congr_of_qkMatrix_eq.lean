-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionQKCircuit_qkScore_congr_of_qkMatrix_eq
-- name    : BookProof.ChapterAttentionQKCircuit.qkScore_congr_of_qkMatrix_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:40:43.487556+00:00
-- url     : https://prove2.me/theorems/d2a09a59-3fc7-43f8-8711-c359ca4acdc8
-- title:
--   `BookProof.ChapterAttentionQKCircuit.qkScore_congr_of_qkMatrix_eq` {WQ₁ WK₁ WQ₂ WK₂ : Matrix (Fin d) (Fin n) ℝ} (h : qkMatrix WQ₁ WK₁ = qkMatrix WQ₂ WK₂) (x y : Fin n → ℝ) :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionQKCircuit`.
--
--   `BookProof.ChapterAttentionQKCircuit.qkScore_congr_of_qkMatrix_eq` {WQ₁ WK₁ WQ₂ WK₂ : Matrix (Fin d) (Fin n) ℝ} (h : qkMatrix WQ₁ WK₁ = qkMatrix WQ₂ WK₂) (x y : Fin n → ℝ) : qkScore WQ₁ WK₁ x y = qkScore WQ₂ WK₂ x y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionQKCircuit.qkScore_congr_of_qkMatrix_eq`.

-- Generated from ChapterAttentionQKCircuit.lean — theorem BookProof.ChapterAttentionQKCircuit.qkScore_congr_of_qkMatrix_eq
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionQKCircuit
open BookProof.ChapterAttentionQKCircuit


open scoped BigOperators

noncomputable section


open Matrix BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {d n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionQKCircuit.qkScore_congr_of_qkMatrix_eq {WQ₁ WK₁ WQ₂ WK₂ : Matrix (Fin d) (Fin n) ℝ}
    (h : qkMatrix WQ₁ WK₁ = qkMatrix WQ₂ WK₂) (x y : Fin n → ℝ) :
    qkScore WQ₁ WK₁ x y = qkScore WQ₂ WK₂ x y := by sorry
