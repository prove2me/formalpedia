-- Prove2me | Theorems.Thm_BookProof_GroupAverage_UnitaryRep_commutes_avgProj
-- name    : BookProof.GroupAverage.UnitaryRep.commutes_avgProj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-24T22:28:11.798214+00:00
-- url     : https://prove2.me/theorems/c7e01892-75f4-4319-90a6-d9a331f4cbcf
-- title:
--   The Lean 4 theorem `commutes_avgProj` in the `ChapterGroupAverageEsa` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.GroupAverage.UnitaryRep.commutes_avgProj` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterGroupAverageEsa.lean — theorem BookProof.GroupAverage.UnitaryRep.commutes_avgProj
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterA
import Definitions.Def_ChapterMaschkeFiniteGroup
import Definitions.Def_ChapterWignerLittleGroup
import Definitions.Def_ChapterA1c
import Theorems.Thm_BookProof_GroupAverage_UnitaryRep_avgProj_mem
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterMaschkeFiniteGroup
import Definitions.Def_ChapterWignerOrbitClassification
open BookProof.ChapterA
open BookProof.ChapterA.System
open BookProof.GroupAverage
open BookProof.ChapterMaschkeFiniteGroup
open BookProof.ChapterWignerLittleGroup



open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {G : Type*} [Group G] [Fintype G]

variable (rep : UnitaryRep G F)
variable {D : Submodule ℂ F}
variable {T : D →ₗ[ℂ] F}

theorem BookProof.GroupAverage.UnitaryRep.commutes_avgProj {hD : ∀ (g : G) (x : F), x ∈ D → rep.act g x ∈ D}
    (hT : ∀ (g : G) (x : D), T ⟨rep.act g (x : F), hD g _ x.2⟩ = rep.act g (T x)) :
    Commutes T (rep.avgProj_mem hD) where
  comm x := by sorry
