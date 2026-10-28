-- Prove2me | Theorems.Thm_BookProof_GroupAverage_UnitaryRep_inner_act_left
-- name    : BookProof.GroupAverage.UnitaryRep.inner_act_left
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-24T22:27:46.703052+00:00
-- url     : https://prove2.me/theorems/2ba200f9-f2f6-4e9c-8d99-1f71349e25e0
-- title:
--   The Lean 4 theorem `inner_act_left` in the `ChapterGroupAverageEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `inner_act_left` in the `ChapterGroupAverageEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGroupAverageEsa.lean

-- Generated from ChapterGroupAverageEsa.lean — theorem BookProof.GroupAverage.UnitaryRep.inner_act_left
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterWignerLittleGroup
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterWignerOrbitClassification
open BookProof.ChapterWignerLittleGroup
open BookProof.GroupAverage



open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {G : Type*} [Group G] [Fintype G]

variable (rep : UnitaryRep G F)

theorem BookProof.GroupAverage.UnitaryRep.inner_act_left (g : G) (x y : F) :
    (inner ℂ (rep.act g x) y : ℂ) = inner ℂ x (rep.act g⁻¹ y) := by sorry
