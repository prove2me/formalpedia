-- Prove2me | Theorems.Thm_BookProof_ChapterCyclicDecomposition_isClosed_cyclicSubspace
-- name    : BookProof.ChapterCyclicDecomposition.isClosed_cyclicSubspace
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:38:13.48389+00:00
-- url     : https://prove2.me/theorems/9a1efa9a-c820-4d69-8bdb-7541db8640e6
-- title:
--   `BookProof.ChapterCyclicDecomposition.isClosed_cyclicSubspace` (xi : H) : IsClosed (cyclicSubspace T hT xi : Set H)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCyclicDecomposition`.
--
--   `BookProof.ChapterCyclicDecomposition.isClosed_cyclicSubspace` (xi : H) : IsClosed (cyclicSubspace T hT xi : Set H)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCyclicDecomposition.isClosed_cyclicSubspace`.

-- Generated from ChapterCyclicDecomposition.lean — theorem BookProof.ChapterCyclicDecomposition.isClosed_cyclicSubspace
import Definitions.Def_ChapterSpectralMultiplication
import Mathlib
import Definitions.Def_ChapterCyclicDecomposition
open BookProof.ChapterCyclicDecomposition


noncomputable section

open MeasureTheory Complex


open BookProof.ChapterSpectralMultiplication

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

theorem BookProof.ChapterCyclicDecomposition.isClosed_cyclicSubspace (xi : H) : IsClosed (cyclicSubspace T hT xi : Set H) := by sorry
