-- Prove2me | Theorems.Thm_BookProof_ChapterSpectralDirectSum_countable_orthogonalCyclicFamily
-- name    : BookProof.ChapterSpectralDirectSum.countable_orthogonalCyclicFamily
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T02:16:48.070788+00:00
-- url     : https://prove2.me/theorems/0e36c5ec-ad4e-4d46-a100-17c894fed62b
-- title:
--   `BookProof.ChapterSpectralDirectSum.countable_orthogonalCyclicFamily` [TopologicalSpace.SeparableSpace H] {S : Set H} (hS : OrthogonalCyclicFamily T hT S) : S.Countable
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSpectralDirectSum`.
--
--   `BookProof.ChapterSpectralDirectSum.countable_orthogonalCyclicFamily` [TopologicalSpace.SeparableSpace H] {S : Set H} (hS : OrthogonalCyclicFamily T hT S) : S.Countable
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSpectralDirectSum.countable_orthogonalCyclicFamily`.

-- Generated from ChapterSpectralDirectSum.lean — theorem BookProof.ChapterSpectralDirectSum.countable_orthogonalCyclicFamily
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Definitions.Def_ChapterCyclicDecomposition
import Definitions.Def_ChapterCyclicDirectSum
import Mathlib
import Definitions.Def_ChapterSpectralDirectSum
open BookProof.ChapterSpectralDirectSum


noncomputable section

open MeasureTheory Complex


open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralMultiplication
open BookProof.ChapterCyclicDecomposition BookProof.ChapterCyclicDirectSum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T) (xi : H)

theorem BookProof.ChapterSpectralDirectSum.countable_orthogonalCyclicFamily [TopologicalSpace.SeparableSpace H] {S : Set H}
    (hS : OrthogonalCyclicFamily T hT S) : S.Countable := by sorry
