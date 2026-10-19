-- Prove2me | Theorems.Thm_BookProof_ChapterSeparableL2Model_continuous_coordMap
-- name    : BookProof.ChapterSeparableL2Model.continuous_coordMap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T02:33:25.313446+00:00
-- url     : https://prove2.me/theorems/34c29b09-0dd2-4fc9-8c28-ff8fd1008b97
-- title:
--   `BookProof.ChapterSeparableL2Model.continuous_coordMap` : Continuous (coordMap D)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSeparableL2Model`.
--
--   `BookProof.ChapterSeparableL2Model.continuous_coordMap` : Continuous (coordMap D)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSeparableL2Model.continuous_coordMap`.

-- Generated from ChapterSeparableL2Model.lean — theorem BookProof.ChapterSeparableL2Model.continuous_coordMap
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterAbelianCyclicModel
import Definitions.Def_ChapterAbelianDirectSum
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterStandardBorelClassification
import Mathlib
import Definitions.Def_ChapterSeparableL2Model
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry
open BookProof.ChapterSeparableL2Model


noncomputable section

open MeasureTheory TopologicalSpace


open BookProof.ChapterAbelianGelfandModel BookProof.ChapterAbelianCyclicModel
open BookProof.ChapterAbelianDirectSum BookProof.ChapterLinftyMultiplication
open BookProof.ChapterStandardBorelClassification

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y] (mu : Measure Y) [IsFiniteMeasure mu] [mu.WeaklyRegular]
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y]
  [BorelSpace Y] (D : Set C(Y, ℂ)) [Countable D]

theorem BookProof.ChapterSeparableL2Model.continuous_coordMap : Continuous (coordMap D) := by sorry
