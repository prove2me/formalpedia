-- Prove2me | Theorems.Thm_BookProof_ChapterSeparableSpectrum_metrizableSpace_characterSpace
-- name    : BookProof.ChapterSeparableSpectrum.metrizableSpace_characterSpace
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T02:42:29.930143+00:00
-- url     : https://prove2.me/theorems/28cab5be-2676-4c48-a3f8-d5799d07a1f2
-- title:
--   `BookProof.ChapterSeparableSpectrum.metrizableSpace_characterSpace` [SeparableSpace A] : MetrizableSpace (characterSpace ℂ A)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSeparableSpectrum`.
--
--   `BookProof.ChapterSeparableSpectrum.metrizableSpace_characterSpace` [SeparableSpace A] : MetrizableSpace (characterSpace ℂ A)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSeparableSpectrum.metrizableSpace_characterSpace`.

-- Generated from ChapterSeparableSpectrum.lean — theorem BookProof.ChapterSeparableSpectrum.metrizableSpace_characterSpace
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

theorem BookProof.ChapterSeparableSpectrum.metrizableSpace_characterSpace [SeparableSpace A] :
    MetrizableSpace (characterSpace ℂ A) := by sorry
