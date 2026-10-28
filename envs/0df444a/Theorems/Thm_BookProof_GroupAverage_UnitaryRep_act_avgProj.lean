-- Prove2me | Theorems.Thm_BookProof_GroupAverage_UnitaryRep_act_avgProj
-- name    : BookProof.GroupAverage.UnitaryRep.act_avgProj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-24T22:27:47.541556+00:00
-- url     : https://prove2.me/theorems/b88ad64b-b10b-43f4-8d71-b9649f937ec3
-- title:
--   The Lean 4 theorem `act_avgProj` in the `ChapterGroupAverageEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `act_avgProj` in the `ChapterGroupAverageEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGroupAverageEsa.lean

-- Generated from ChapterGroupAverageEsa.lean — theorem BookProof.GroupAverage.UnitaryRep.act_avgProj
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterMaschkeFiniteGroup
import Definitions.Def_ChapterWignerLittleGroup
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterMaschkeFiniteGroup
import Definitions.Def_ChapterWignerOrbitClassification
open BookProof.ChapterMaschkeFiniteGroup
open BookProof.ChapterWignerLittleGroup
open BookProof.GroupAverage



open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {G : Type*} [Group G] [Fintype G]

variable (rep : UnitaryRep G F)
variable (G) in

theorem BookProof.GroupAverage.UnitaryRep.act_avgProj (h : G) (x : F) : rep.act h (rep.avgProj x) = rep.avgProj x := by sorry
