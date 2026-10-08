-- Prove2me | Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_gen_stoneGroup_eq
-- name    : BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.gen_stoneGroup_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-04T13:49:36.912575+00:00
-- url     : https://prove2.me/theorems/1341ef0c-572f-4dd3-8883-f241c83a023c
-- title:
--   The Lean 4 theorem `gen_stoneGroup_eq` in the `ChapterStoneTheorem` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.gen_stoneGroup_eq` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterStoneTheorem.lean — theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.gen_stoneGroup_eq
import Mathlib
import Definitions.Def_ChapterStoneTheorem
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup
open BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [TopologicalSpace.SeparableSpace H]


open scoped InnerProductSpace

theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.gen_stoneGroup_eq (T : UnboundedSelfAdjoint H) : T.stoneGroup.gen = T := by sorry
