-- Prove2me | Theorems.Thm_BookProof_GroupAverage_UnitaryRep_act_sum
-- name    : BookProof.GroupAverage.UnitaryRep.act_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:57:51.759632+00:00
-- url     : https://prove2.me/theorems/8b587980-267f-4b11-8e2f-462331959cad
-- title:
--   The Lean 4 theorem `act_sum` in the `ChapterGroupAverageEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `act_sum` in the `ChapterGroupAverageEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGroupAverageEsa.lean

-- Generated from ChapterGroupAverageEsa.lean — theorem BookProof.GroupAverage.UnitaryRep.act_sum
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterWignerLittleGroup
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterWignerOrbitClassification
open BookProof.ChapterWignerLittleGroup



open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa
open BookProof.GroupAverage

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {G : Type*} [Group G] [Fintype G]

variable (rep : UnitaryRep G F)
variable (G) in

theorem BookProof.GroupAverage.UnitaryRep.act_sum (h : G) (x : F) :
    rep.act h (∑ g : G, rep.act g x) = ∑ g : G, rep.act g x := by sorry
