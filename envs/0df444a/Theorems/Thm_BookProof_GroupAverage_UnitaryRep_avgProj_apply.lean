-- Prove2me | Theorems.Thm_BookProof_GroupAverage_UnitaryRep_avgProj_apply
-- name    : BookProof.GroupAverage.UnitaryRep.avgProj_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T04:58:19.451981+00:00
-- url     : https://prove2.me/theorems/04ba135e-ab9e-499d-9b68-323456b8e1c5
-- title:
--   The Lean 4 theorem `avgProj_apply` in the `ChapterGroupAverageEsa` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.GroupAverage.UnitaryRep.avgProj_apply` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterGroupAverageEsa.lean — theorem BookProof.GroupAverage.UnitaryRep.avgProj_apply
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
variable (G) in

theorem BookProof.GroupAverage.UnitaryRep.avgProj_apply (x : F) :
    rep.avgProj x = ((Fintype.card G : ℂ))⁻¹ • ∑ g : G, rep.act g x := by sorry
