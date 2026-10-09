-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionOutput_headOutput_mem_convexHull
-- name    : BookProof.ChapterAttentionOutput.headOutput_mem_convexHull
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:33:16.224986+00:00
-- url     : https://prove2.me/theorems/e4acc56e-66b8-4e5a-85e0-7a2791ceeec2
-- title:
--   `BookProof.ChapterAttentionOutput.headOutput_mem_convexHull` (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) (i : Fin m) : headOutput beta s v ∈ convexHull ℝ (Set.range v)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionOutput`.
--
--   `BookProof.ChapterAttentionOutput.headOutput_mem_convexHull` (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) (i : Fin m) : headOutput beta s v ∈ convexHull ℝ (Set.range v)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionOutput.headOutput_mem_convexHull`.

-- Generated from ChapterAttentionOutput.lean — theorem BookProof.ChapterAttentionOutput.headOutput_mem_convexHull
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionOutput
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionOutput


open scoped BigOperators

open Filter Topology

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionOutput.headOutput_mem_convexHull (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) (i : Fin m) :
    headOutput beta s v ∈ convexHull ℝ (Set.range v) := by sorry
