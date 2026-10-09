-- Prove2me | Theorems.Thm_BookProof_GroupAverage_UnitaryRep_avgProj_mem
-- name    : BookProof.GroupAverage.UnitaryRep.avgProj_mem
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T04:57:07.926979+00:00
-- url     : https://prove2.me/theorems/b90fb11b-ab4e-4a5e-b844-cf0718fdf2c5
-- title:
--   The Lean 4 theorem `avgProj_mem` in the `ChapterGroupAverageEsa` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.GroupAverage.UnitaryRep.avgProj_mem` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterGroupAverageEsa.lean — theorem BookProof.GroupAverage.UnitaryRep.avgProj_mem
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterMaschkeFiniteGroup
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterMaschkeFiniteGroup
open BookProof.ChapterWignerLittleGroup
open BookProof.GroupAverage
open BookProof.GroupAverage



open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {G : Type*} [Group G] [Fintype G]

variable (rep : UnitaryRep G F)
variable {D : Submodule ℂ F}

theorem BookProof.GroupAverage.UnitaryRep.avgProj_mem (hD : ∀ (g : G) (x : F), x ∈ D → rep.act g x ∈ D) :
    ∀ x ∈ D, rep.avgProj x ∈ D := by sorry
