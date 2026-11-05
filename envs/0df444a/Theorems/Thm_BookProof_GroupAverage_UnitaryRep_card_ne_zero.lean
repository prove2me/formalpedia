-- Prove2me | Theorems.Thm_BookProof_GroupAverage_UnitaryRep_card_ne_zero
-- name    : BookProof.GroupAverage.UnitaryRep.card_ne_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:59:02.354611+00:00
-- url     : https://prove2.me/theorems/136bd1ec-a4a8-436d-852c-feacea75a8f0
-- title:
--   The Lean 4 theorem `card_ne_zero` in the `ChapterGroupAverageEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `card_ne_zero` in the `ChapterGroupAverageEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGroupAverageEsa.lean

-- Generated from ChapterGroupAverageEsa.lean — theorem BookProof.GroupAverage.UnitaryRep.card_ne_zero
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterGroupAverageEsa



open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa
open BookProof.GroupAverage

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {G : Type*} [Group G] [Fintype G]

variable (rep : UnitaryRep G F)
variable (G) in

theorem BookProof.GroupAverage.UnitaryRep.card_ne_zero : (Fintype.card G : ℂ) ≠ 0 := by sorry
