-- Prove2me | Theorems.Thm_BookProof_ChapterSeparableSpectrum_separableSpace_continuousMap_characterSpace
-- name    : BookProof.ChapterSeparableSpectrum.separableSpace_continuousMap_characterSpace
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T02:41:00.080999+00:00
-- url     : https://prove2.me/theorems/1a37bb34-6667-4f67-8b7a-d72fcd25fc81
-- title:
--   `BookProof.ChapterSeparableSpectrum.separableSpace_continuousMap_characterSpace` [SeparableSpace A] : SeparableSpace C(characterSpace ℂ A, ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSeparableSpectrum`.
--
--   `BookProof.ChapterSeparableSpectrum.separableSpace_continuousMap_characterSpace` [SeparableSpace A] : SeparableSpace C(characterSpace ℂ A, ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSeparableSpectrum.separableSpace_continuousMap_characterSpace`.

-- Generated from ChapterSeparableSpectrum.lean — theorem BookProof.ChapterSeparableSpectrum.separableSpace_continuousMap_characterSpace
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterAbelianDirectSum
import Definitions.Def_ChapterStandardBorelClassification
import Mathlib
import Definitions.Def_ChapterSeparableSpectrum
open BookProof.ChapterSeparableSpectrum


noncomputable section

open MeasureTheory TopologicalSpace WeakDual


open BookProof.ChapterAbelianGelfandModel BookProof.ChapterAbelianDirectSum
open BookProof.ChapterStandardBorelClassification

variable (Y : Type*) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
  [SeparableSpace C(Y, ℂ)] [MeasurableSpace Y] [BorelSpace Y]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : Type*) [CommCStarAlgebra A]

theorem BookProof.ChapterSeparableSpectrum.separableSpace_continuousMap_characterSpace [SeparableSpace A] :
    SeparableSpace C(characterSpace ℂ A, ℂ) := by sorry
