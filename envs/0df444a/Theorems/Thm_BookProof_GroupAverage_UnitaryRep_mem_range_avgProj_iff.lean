-- Prove2me | Theorems.Thm_BookProof_GroupAverage_UnitaryRep_mem_range_avgProj_iff
-- name    : BookProof.GroupAverage.UnitaryRep.mem_range_avgProj_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-04T13:52:32.398981+00:00
-- url     : https://prove2.me/theorems/1d254b9a-f47e-44c5-ab19-2c370c34d96f
-- title:
--   The Lean 4 theorem `mem_range_avgProj_iff` in the `ChapterGroupAverageEsa` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.GroupAverage.UnitaryRep.mem_range_avgProj_iff` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterGroupAverageEsa.lean — theorem BookProof.GroupAverage.UnitaryRep.mem_range_avgProj_iff
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterMaschkeFiniteGroup
import Definitions.Def_ChapterWignerLittleGroup
import Definitions.Def_ChapterA4
open BookProof.ChapterMaschkeFiniteGroup
open BookProof.ChapterWignerLittleGroup
open BookProof.GroupAverage
open BookProof.GroupAverage

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {G : Type*} [Group G] [Fintype G]
variable (rep : UnitaryRep G F)
variable (G) in



open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa

noncomputable section

theorem BookProof.GroupAverage.UnitaryRep.mem_range_avgProj_iff {x : F} :
    x ∈ LinearMap.range rep.avgProj ↔ ∀ g : G, rep.act g x = x := by sorry
