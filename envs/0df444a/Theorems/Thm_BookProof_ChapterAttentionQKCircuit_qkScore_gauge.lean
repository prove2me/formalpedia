-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionQKCircuit_qkScore_gauge
-- name    : BookProof.ChapterAttentionQKCircuit.qkScore_gauge
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:40:53.080602+00:00
-- url     : https://prove2.me/theorems/39b6b4fe-b8a0-411b-98a0-9007e2ce9c41
-- title:
--   `BookProof.ChapterAttentionQKCircuit.qkScore_gauge` {A B : Matrix (Fin d) (Fin d) ℝ} (hAB : Aᵀ * B = 1) (WQ WK : Matrix (Fin d) (Fin n) ℝ) (x y : Fin n → ℝ) : qkScore (A * WQ) (B *
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionQKCircuit`.
--
--   `BookProof.ChapterAttentionQKCircuit.qkScore_gauge` {A B : Matrix (Fin d) (Fin d) ℝ} (hAB : Aᵀ * B = 1) (WQ WK : Matrix (Fin d) (Fin n) ℝ) (x y : Fin n → ℝ) : qkScore (A * WQ) (B * WK) x y = qkScore WQ WK x y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionQKCircuit.qkScore_gauge`.

-- Generated from ChapterAttentionQKCircuit.lean — theorem BookProof.ChapterAttentionQKCircuit.qkScore_gauge
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionQKCircuit
open BookProof.ChapterAttentionQKCircuit


open scoped BigOperators

noncomputable section


open Matrix BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {d n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionQKCircuit.qkScore_gauge {A B : Matrix (Fin d) (Fin d) ℝ} (hAB : Aᵀ * B = 1)
    (WQ WK : Matrix (Fin d) (Fin n) ℝ) (x y : Fin n → ℝ) :
    qkScore (A * WQ) (B * WK) x y = qkScore WQ WK x y := by sorry
