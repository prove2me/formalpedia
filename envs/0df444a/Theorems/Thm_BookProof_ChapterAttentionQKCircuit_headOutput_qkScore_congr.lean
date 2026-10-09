-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionQKCircuit_headOutput_qkScore_congr
-- name    : BookProof.ChapterAttentionQKCircuit.headOutput_qkScore_congr
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:43:05.950958+00:00
-- url     : https://prove2.me/theorems/e4d7585d-c53d-492d-a697-12c7d381e942
-- title:
--   `BookProof.ChapterAttentionQKCircuit.headOutput_qkScore_congr` (beta : ℝ) {WQ₁ WK₁ WQ₂ WK₂ : Matrix (Fin d) (Fin n) ℝ} (h : qkMatrix WQ₁ WK₁ = qkMatrix WQ₂ WK₂) (x : Fin n...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionQKCircuit`.
--
--   `BookProof.ChapterAttentionQKCircuit.headOutput_qkScore_congr` (beta : ℝ) {WQ₁ WK₁ WQ₂ WK₂ : Matrix (Fin d) (Fin n) ℝ} (h : qkMatrix WQ₁ WK₁ = qkMatrix WQ₂ WK₂) (x : Fin n → ℝ) (k : Fin m → Fin n → ℝ) (v : Fin m → E) : headOutput beta (fun l => qkScore WQ₁ WK₁ x (k l)) v = headOutput beta (fun l => qkScore WQ₂ WK₂ x (k l)) v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionQKCircuit.headOutput_qkScore_congr`.

-- Generated from ChapterAttentionQKCircuit.lean — theorem BookProof.ChapterAttentionQKCircuit.headOutput_qkScore_congr
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionQKCircuit
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterAttentionQKCircuit


open scoped BigOperators

noncomputable section


open Matrix BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterAttentionOutput

variable {d n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionQKCircuit.headOutput_qkScore_congr (beta : ℝ) {WQ₁ WK₁ WQ₂ WK₂ : Matrix (Fin d) (Fin n) ℝ}
    (h : qkMatrix WQ₁ WK₁ = qkMatrix WQ₂ WK₂) (x : Fin n → ℝ) (k : Fin m → Fin n → ℝ)
    (v : Fin m → E) :
    headOutput beta (fun l => qkScore WQ₁ WK₁ x (k l)) v
      = headOutput beta (fun l => qkScore WQ₂ WK₂ x (k l)) v := by sorry
