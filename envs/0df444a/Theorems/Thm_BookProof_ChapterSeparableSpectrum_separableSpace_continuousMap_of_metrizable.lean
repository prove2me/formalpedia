-- Prove2me | Theorems.Thm_BookProof_ChapterSeparableSpectrum_separableSpace_continuousMap_of_metrizable
-- name    : BookProof.ChapterSeparableSpectrum.separableSpace_continuousMap_of_metrizable
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T02:41:08.200736+00:00
-- url     : https://prove2.me/theorems/d41db28c-fb4a-48cc-9746-5fc86f981b7d
-- title:
--   `BookProof.ChapterSeparableSpectrum.separableSpace_continuousMap_of_metrizable` [MetrizableSpace Y] : SeparableSpace C(Y, ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSeparableSpectrum`.
--
--   `BookProof.ChapterSeparableSpectrum.separableSpace_continuousMap_of_metrizable` [MetrizableSpace Y] : SeparableSpace C(Y, ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSeparableSpectrum.separableSpace_continuousMap_of_metrizable`.

-- Generated from ChapterSeparableSpectrum.lean — theorem BookProof.ChapterSeparableSpectrum.separableSpace_continuousMap_of_metrizable
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

theorem BookProof.ChapterSeparableSpectrum.separableSpace_continuousMap_of_metrizable [MetrizableSpace Y] :
    SeparableSpace C(Y, ℂ) := by sorry
