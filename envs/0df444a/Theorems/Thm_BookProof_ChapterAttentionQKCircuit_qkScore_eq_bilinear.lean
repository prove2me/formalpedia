-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionQKCircuit_qkScore_eq_bilinear
-- name    : BookProof.ChapterAttentionQKCircuit.qkScore_eq_bilinear
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:40:39.797228+00:00
-- url     : https://prove2.me/theorems/de8e1298-9f3f-40fb-88f0-8aee3adcc26b
-- title:
--   `BookProof.ChapterAttentionQKCircuit.qkScore_eq_bilinear` (WQ WK : Matrix (Fin d) (Fin n) ℝ) (x y : Fin n → ℝ) : qkScore WQ WK x y = x ⬝ᵥ (qkMatrix WQ WK *ᵥ y)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionQKCircuit`.
--
--   `BookProof.ChapterAttentionQKCircuit.qkScore_eq_bilinear` (WQ WK : Matrix (Fin d) (Fin n) ℝ) (x y : Fin n → ℝ) : qkScore WQ WK x y = x ⬝ᵥ (qkMatrix WQ WK *ᵥ y)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionQKCircuit.qkScore_eq_bilinear`.

-- Generated from ChapterAttentionQKCircuit.lean — theorem BookProof.ChapterAttentionQKCircuit.qkScore_eq_bilinear
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionQKCircuit
open BookProof.ChapterAttentionQKCircuit


open scoped BigOperators

noncomputable section


open Matrix BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {d n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionQKCircuit.qkScore_eq_bilinear (WQ WK : Matrix (Fin d) (Fin n) ℝ) (x y : Fin n → ℝ) :
    qkScore WQ WK x y = x ⬝ᵥ (qkMatrix WQ WK *ᵥ y) := by sorry
