-- Prove2me | Theorems.Thm_BookProof_GroupAverage_UnitaryRep_avgProj_of_invariant
-- name    : BookProof.GroupAverage.UnitaryRep.avgProj_of_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-24T22:27:47.751979+00:00
-- url     : https://prove2.me/theorems/f963ba5a-c7d8-4736-a24a-8787f42fdbaf
-- title:
--   The Lean 4 theorem `avgProj_of_invariant` in the `ChapterGroupAverageEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `avgProj_of_invariant` in the `ChapterGroupAverageEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGroupAverageEsa.lean

-- Generated from ChapterGroupAverageEsa.lean — theorem BookProof.GroupAverage.UnitaryRep.avgProj_of_invariant
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

theorem BookProof.GroupAverage.UnitaryRep.avgProj_of_invariant {x : F} (hx : ∀ g : G, rep.act g x = x) : rep.avgProj x = x := by sorry
