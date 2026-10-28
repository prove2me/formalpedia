-- Prove2me | Theorems.Thm_BookProof_GroupAverage_UnitaryRep_isReducingProjection_avgProj
-- name    : BookProof.GroupAverage.UnitaryRep.isReducingProjection_avgProj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-24T22:27:42.594628+00:00
-- url     : https://prove2.me/theorems/b30b0add-680a-4231-addd-5301703b84bd
-- title:
--   The Lean 4 theorem `isReducingProjection_avgProj` in the `ChapterGroupAverageEsa` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.GroupAverage.UnitaryRep.isReducingProjection_avgProj` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterGroupAverageEsa.lean — theorem BookProof.GroupAverage.UnitaryRep.isReducingProjection_avgProj
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

theorem BookProof.GroupAverage.UnitaryRep.isReducingProjection_avgProj : IsReducingProjection rep.avgProj := by sorry
