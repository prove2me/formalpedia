-- Prove2me | Theorems.Thm_BookProof_ChapterStoneTheorem_stone_bijection
-- name    : BookProof.ChapterStoneTheorem.stone_bijection
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-02T13:16:35.254486+00:00
-- url     : https://prove2.me/theorems/7b07bd91-a0a9-4cf9-90ec-7c7d872d09c4
-- title:
--   The Lean 4 theorem `stone_bijection` in the `ChapterStoneTheorem` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `stone_bijection` in the `ChapterStoneTheorem` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStoneTheorem.lean

-- Generated from ChapterStoneTheorem.lean — theorem BookProof.ChapterStoneTheorem.stone_bijection
import Mathlib
import Definitions.Def_ChapterStoneTheorem
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneMeasurable
import Definitions.Def_ChapterStoneResolvent
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup
open BookProof.ChapterStoneTheorem


open scoped InnerProductSpace
open BookProof.ChapterStoneResolvent


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [TopologicalSpace.SeparableSpace H]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem BookProof.ChapterStoneTheorem.stone_bijection :
    Function.Bijective (fun T : UnboundedSelfAdjoint H => T.stoneGroup) := by sorry
