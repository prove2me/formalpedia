-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionOVCircuit_mulVec_headOutput
-- name    : BookProof.ChapterAttentionOVCircuit.mulVec_headOutput
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:32:35.914976+00:00
-- url     : https://prove2.me/theorems/c0b5222d-d1c8-4b75-9423-3e9a7635c8f3
-- title:
--   `BookProof.ChapterAttentionOVCircuit.mulVec_headOutput` (A : Matrix (Fin p) (Fin n) ℝ) (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → (Fin n → ℝ)) : A *ᵥ headOutput beta s v = headOutput
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionOVCircuit`.
--
--   `BookProof.ChapterAttentionOVCircuit.mulVec_headOutput` (A : Matrix (Fin p) (Fin n) ℝ) (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → (Fin n → ℝ)) : A *ᵥ headOutput beta s v = headOutput beta s (fun j => A *ᵥ v j)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionOVCircuit.mulVec_headOutput`.

-- Generated from ChapterAttentionOVCircuit.lean — theorem BookProof.ChapterAttentionOVCircuit.mulVec_headOutput
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionOVCircuit
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionOVCircuit


open scoped BigOperators

noncomputable section


open Matrix BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterAttentionOutput

variable {d n p m : ℕ}

theorem BookProof.ChapterAttentionOVCircuit.mulVec_headOutput (A : Matrix (Fin p) (Fin n) ℝ) (beta : ℝ) (s : Fin m → ℝ)
    (v : Fin m → (Fin n → ℝ)) :
    A *ᵥ headOutput beta s v = headOutput beta s (fun j => A *ᵥ v j) := by sorry
