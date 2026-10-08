-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionOVCircuit_ovOutput_mem_range
-- name    : BookProof.ChapterAttentionOVCircuit.ovOutput_mem_range
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:33:33.410489+00:00
-- url     : https://prove2.me/theorems/66cc0105-5b2c-4397-9742-80e040b65ee6
-- title:
--   `BookProof.ChapterAttentionOVCircuit.ovOutput_mem_range` (beta : ℝ) (s : Fin m → ℝ) (WO : Matrix (Fin n) (Fin d) ℝ) (WV : Matrix (Fin d) (Fin n) ℝ) (x : Fin m → (Fin n → ℝ)) : ovOu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionOVCircuit`.
--
--   `BookProof.ChapterAttentionOVCircuit.ovOutput_mem_range` (beta : ℝ) (s : Fin m → ℝ) (WO : Matrix (Fin n) (Fin d) ℝ) (WV : Matrix (Fin d) (Fin n) ℝ) (x : Fin m → (Fin n → ℝ)) : ovOutput beta s WO WV x ∈ LinearMap.range (Matrix.mulVecLin WO)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionOVCircuit.ovOutput_mem_range`.

-- Generated from ChapterAttentionOVCircuit.lean — theorem BookProof.ChapterAttentionOVCircuit.ovOutput_mem_range
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionOVCircuit
open BookProof.ChapterAttentionOVCircuit


open scoped BigOperators

noncomputable section


open Matrix BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {d n p m : ℕ}

theorem BookProof.ChapterAttentionOVCircuit.ovOutput_mem_range (beta : ℝ) (s : Fin m → ℝ) (WO : Matrix (Fin n) (Fin d) ℝ)
    (WV : Matrix (Fin d) (Fin n) ℝ) (x : Fin m → (Fin n → ℝ)) :
    ovOutput beta s WO WV x ∈ LinearMap.range (Matrix.mulVecLin WO) := by sorry
