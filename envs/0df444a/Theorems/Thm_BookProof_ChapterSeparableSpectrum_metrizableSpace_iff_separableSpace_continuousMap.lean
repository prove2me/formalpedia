-- Prove2me | Theorems.Thm_BookProof_ChapterSeparableSpectrum_metrizableSpace_iff_separableSpace_continuousMap
-- name    : BookProof.ChapterSeparableSpectrum.metrizableSpace_iff_separableSpace_continuousMap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T02:40:44.668985+00:00
-- url     : https://prove2.me/theorems/e76714d8-4441-4311-be1c-d0652f61a672
-- title:
--   `BookProof.ChapterSeparableSpectrum.metrizableSpace_iff_separableSpace_continuousMap` : MetrizableSpace Y ↔ SeparableSpace C(Y, ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSeparableSpectrum`.
--
--   `BookProof.ChapterSeparableSpectrum.metrizableSpace_iff_separableSpace_continuousMap` : MetrizableSpace Y ↔ SeparableSpace C(Y, ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSeparableSpectrum.metrizableSpace_iff_separableSpace_continuousMap`.

-- Generated from ChapterSeparableSpectrum.lean — theorem BookProof.ChapterSeparableSpectrum.metrizableSpace_iff_separableSpace_continuousMap
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

theorem BookProof.ChapterSeparableSpectrum.metrizableSpace_iff_separableSpace_continuousMap :
    MetrizableSpace Y ↔ SeparableSpace C(Y, ℂ) := by sorry
