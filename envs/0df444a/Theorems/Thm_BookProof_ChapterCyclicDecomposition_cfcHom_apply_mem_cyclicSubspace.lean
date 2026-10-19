-- Prove2me | Theorems.Thm_BookProof_ChapterCyclicDecomposition_cfcHom_apply_mem_cyclicSubspace
-- name    : BookProof.ChapterCyclicDecomposition.cfcHom_apply_mem_cyclicSubspace
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:38:06.446155+00:00
-- url     : https://prove2.me/theorems/dcadda5b-428d-4659-8fe4-3dd509a43c28
-- title:
--   `BookProof.ChapterCyclicDecomposition.cfcHom_apply_mem_cyclicSubspace` (xi : H) (g : C(spectrum ℂ T, ℂ)) : cfcHom hT g xi ∈ cyclicSubspace T hT xi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCyclicDecomposition`.
--
--   `BookProof.ChapterCyclicDecomposition.cfcHom_apply_mem_cyclicSubspace` (xi : H) (g : C(spectrum ℂ T, ℂ)) : cfcHom hT g xi ∈ cyclicSubspace T hT xi
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCyclicDecomposition.cfcHom_apply_mem_cyclicSubspace`.

-- Generated from ChapterCyclicDecomposition.lean — theorem BookProof.ChapterCyclicDecomposition.cfcHom_apply_mem_cyclicSubspace
import Definitions.Def_ChapterSpectralMultiplication
import Mathlib
import Definitions.Def_ChapterCyclicDecomposition
open BookProof.ChapterCyclicDecomposition


noncomputable section

open MeasureTheory Complex


open BookProof.ChapterSpectralMultiplication

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

theorem BookProof.ChapterCyclicDecomposition.cfcHom_apply_mem_cyclicSubspace (xi : H) (g : C(spectrum ℂ T, ℂ)) :
    cfcHom hT g xi ∈ cyclicSubspace T hT xi := by sorry
