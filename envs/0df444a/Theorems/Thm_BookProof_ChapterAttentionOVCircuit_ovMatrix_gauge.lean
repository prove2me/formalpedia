-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionOVCircuit_ovMatrix_gauge
-- name    : BookProof.ChapterAttentionOVCircuit.ovMatrix_gauge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:32:45.603297+00:00
-- url     : https://prove2.me/theorems/7e2f973a-5329-4b88-9f4c-47c23d069f14
-- title:
--   `BookProof.ChapterAttentionOVCircuit.ovMatrix_gauge` {A B : Matrix (Fin d) (Fin d) ℝ} (hAB : A * B = 1) (WO : Matrix (Fin n) (Fin d) ℝ) (WV : Matrix (Fin d) (Fin n) ℝ) : ovMatrix (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionOVCircuit`.
--
--   `BookProof.ChapterAttentionOVCircuit.ovMatrix_gauge` {A B : Matrix (Fin d) (Fin d) ℝ} (hAB : A * B = 1) (WO : Matrix (Fin n) (Fin d) ℝ) (WV : Matrix (Fin d) (Fin n) ℝ) : ovMatrix (WO * A) (B * WV) = ovMatrix WO WV
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionOVCircuit.ovMatrix_gauge`.

-- Generated from ChapterAttentionOVCircuit.lean — theorem BookProof.ChapterAttentionOVCircuit.ovMatrix_gauge
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionOVCircuit
open BookProof.ChapterAttentionOVCircuit


open scoped BigOperators

noncomputable section


open Matrix BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {d n p m : ℕ}

theorem BookProof.ChapterAttentionOVCircuit.ovMatrix_gauge {A B : Matrix (Fin d) (Fin d) ℝ} (hAB : A * B = 1)
    (WO : Matrix (Fin n) (Fin d) ℝ) (WV : Matrix (Fin d) (Fin n) ℝ) :
    ovMatrix (WO * A) (B * WV) = ovMatrix WO WV := by sorry
