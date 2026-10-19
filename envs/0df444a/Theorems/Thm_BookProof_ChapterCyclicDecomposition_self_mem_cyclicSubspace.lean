-- Prove2me | Theorems.Thm_BookProof_ChapterCyclicDecomposition_self_mem_cyclicSubspace
-- name    : BookProof.ChapterCyclicDecomposition.self_mem_cyclicSubspace
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:37:53.78337+00:00
-- url     : https://prove2.me/theorems/9273219a-b6e2-4cbb-929f-17f0d93e7d74
-- title:
--   `BookProof.ChapterCyclicDecomposition.self_mem_cyclicSubspace` (xi : H) : xi ∈ cyclicSubspace T hT xi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCyclicDecomposition`.
--
--   `BookProof.ChapterCyclicDecomposition.self_mem_cyclicSubspace` (xi : H) : xi ∈ cyclicSubspace T hT xi
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCyclicDecomposition.self_mem_cyclicSubspace`.

-- Generated from ChapterCyclicDecomposition.lean — theorem BookProof.ChapterCyclicDecomposition.self_mem_cyclicSubspace
import Definitions.Def_ChapterSpectralMultiplication
import Mathlib
import Definitions.Def_ChapterCyclicDecomposition
open BookProof.ChapterCyclicDecomposition


noncomputable section

open MeasureTheory Complex


open BookProof.ChapterSpectralMultiplication

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

theorem BookProof.ChapterCyclicDecomposition.self_mem_cyclicSubspace (xi : H) : xi ∈ cyclicSubspace T hT xi := by sorry
