-- Prove2me | Theorems.Thm_BookProof_ChapterSeparableSpectrum_metrizableSpace_of_separable_continuousMap
-- name    : BookProof.ChapterSeparableSpectrum.metrizableSpace_of_separable_continuousMap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T02:40:34.46899+00:00
-- url     : https://prove2.me/theorems/dae61f75-6821-49b2-8b2d-e61dac72920e
-- title:
--   `BookProof.ChapterSeparableSpectrum.metrizableSpace_of_separable_continuousMap` [SeparableSpace C(Y, ℂ)] : MetrizableSpace Y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSeparableSpectrum`.
--
--   `BookProof.ChapterSeparableSpectrum.metrizableSpace_of_separable_continuousMap` [SeparableSpace C(Y, ℂ)] : MetrizableSpace Y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSeparableSpectrum.metrizableSpace_of_separable_continuousMap`.

-- Generated from ChapterSeparableSpectrum.lean — theorem BookProof.ChapterSeparableSpectrum.metrizableSpace_of_separable_continuousMap
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

theorem BookProof.ChapterSeparableSpectrum.metrizableSpace_of_separable_continuousMap [SeparableSpace C(Y, ℂ)] :
    MetrizableSpace Y := by sorry
