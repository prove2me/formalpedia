-- Prove2me | Theorems.Thm_BookProof_ChapterCyclicDecomposition_invariant_cyclicSubspace
-- name    : BookProof.ChapterCyclicDecomposition.invariant_cyclicSubspace
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:38:20.327954+00:00
-- url     : https://prove2.me/theorems/50ec252b-b608-4f9f-80ba-e7eafe0c9b1c
-- title:
--   `BookProof.ChapterCyclicDecomposition.invariant_cyclicSubspace` (xi : H) : Invariant T hT (cyclicSubspace T hT xi)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCyclicDecomposition`.
--
--   `BookProof.ChapterCyclicDecomposition.invariant_cyclicSubspace` (xi : H) : Invariant T hT (cyclicSubspace T hT xi)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCyclicDecomposition.invariant_cyclicSubspace`.

-- Generated from ChapterCyclicDecomposition.lean — theorem BookProof.ChapterCyclicDecomposition.invariant_cyclicSubspace
import Definitions.Def_ChapterSpectralMultiplication
import Mathlib
import Definitions.Def_ChapterCyclicDecomposition
open BookProof.ChapterCyclicDecomposition


noncomputable section

open MeasureTheory Complex


open BookProof.ChapterSpectralMultiplication

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

theorem BookProof.ChapterCyclicDecomposition.invariant_cyclicSubspace (xi : H) : Invariant T hT (cyclicSubspace T hT xi) := by sorry
