-- Prove2me | Theorems.Thm_BookProof_ChapterSeparableL2Model_separableSpace_of_linearIsometry
-- name    : BookProof.ChapterSeparableL2Model.separableSpace_of_linearIsometry
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-02T20:42:49.315245+00:00
-- url     : https://prove2.me/theorems/9ccfe98a-bbbf-486c-96b8-2c59efee75fc
-- title:
--   `BookProof.ChapterSeparableL2Model.separableSpace_of_linearIsometry` [SeparableSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (V : E →ₗᵢ[ℂ] H) : SeparableSpace E
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSeparableL2Model`.
--
--   `BookProof.ChapterSeparableL2Model.separableSpace_of_linearIsometry` [SeparableSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (V : E →ₗᵢ[ℂ] H) : SeparableSpace E
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSeparableL2Model.separableSpace_of_linearIsometry`.

-- Generated from ChapterSeparableL2Model.lean — theorem BookProof.ChapterSeparableL2Model.separableSpace_of_linearIsometry
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterAbelianCyclicModel
import Definitions.Def_ChapterAbelianDirectSum
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterStandardBorelClassification
import Mathlib
import Definitions.Def_ChapterSeparableL2Model
import Definitions.Def_ChapterSeparableL2Model
open BookProof.ChapterSeparableL2Model


noncomputable section

open MeasureTheory TopologicalSpace


open BookProof.ChapterAbelianGelfandModel BookProof.ChapterAbelianCyclicModel
open BookProof.ChapterAbelianDirectSum BookProof.ChapterLinftyMultiplication
open BookProof.ChapterStandardBorelClassification

universe u

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y] (mu : Measure Y) [IsFiniteMeasure mu] [mu.WeaklyRegular]
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y]
  [BorelSpace Y] (D : Set C(Y, ℂ)) [Countable D]
variable {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y] (mu : Measure Y) [IsProbabilityMeasure mu] [mu.WeaklyRegular]
variable {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.ChapterSeparableL2Model.separableSpace_of_linearIsometry [SeparableSpace H] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (V : E →ₗᵢ[ℂ] H) : SeparableSpace E := by sorry
