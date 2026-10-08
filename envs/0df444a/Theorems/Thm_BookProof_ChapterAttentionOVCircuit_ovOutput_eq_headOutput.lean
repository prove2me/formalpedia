-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionOVCircuit_ovOutput_eq_headOutput
-- name    : BookProof.ChapterAttentionOVCircuit.ovOutput_eq_headOutput
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:32:56.534635+00:00
-- url     : https://prove2.me/theorems/169b91d0-96c7-436e-83c5-c18e823726b6
-- title:
--   `BookProof.ChapterAttentionOVCircuit.ovOutput_eq_headOutput` (beta : ℝ) (s : Fin m → ℝ) (WO : Matrix (Fin n) (Fin d) ℝ) (WV : Matrix (Fin d) (Fin n) ℝ) (x : Fin m → (Fin n → ℝ)) :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionOVCircuit`.
--
--   `BookProof.ChapterAttentionOVCircuit.ovOutput_eq_headOutput` (beta : ℝ) (s : Fin m → ℝ) (WO : Matrix (Fin n) (Fin d) ℝ) (WV : Matrix (Fin d) (Fin n) ℝ) (x : Fin m → (Fin n → ℝ)) : ovOutput beta s WO WV x = headOutput beta s (fun j => ovMatrix WO WV *ᵥ x j)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionOVCircuit.ovOutput_eq_headOutput`.

-- Generated from ChapterAttentionOVCircuit.lean — theorem BookProof.ChapterAttentionOVCircuit.ovOutput_eq_headOutput
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionOVCircuit
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterAttentionOVCircuit


open scoped BigOperators

noncomputable section


open Matrix BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterAttentionOutput

variable {d n p m : ℕ}

theorem BookProof.ChapterAttentionOVCircuit.ovOutput_eq_headOutput (beta : ℝ) (s : Fin m → ℝ) (WO : Matrix (Fin n) (Fin d) ℝ)
    (WV : Matrix (Fin d) (Fin n) ℝ) (x : Fin m → (Fin n → ℝ)) :
    ovOutput beta s WO WV x = headOutput beta s (fun j => ovMatrix WO WV *ᵥ x j) := by sorry
