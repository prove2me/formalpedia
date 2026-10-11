-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_latticeFullData_advection_apply
-- name    : BookProof.NavierStokesFlow.FullEsa.latticeFullData_advection_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T08:14:30.533237+00:00
-- url     : https://prove2.me/theorems/5329aa06-715f-48e5-974f-50f4c08fe4d5
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.latticeFullData_advection_apply` (v : Fin 15 → LinfZ) (nu : ℝ) (i : Fin 3) (x : (latticeFullData v nu).D) : ((latticeFullData v nu).advection i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.latticeFullData_advection_apply` (v : Fin 15 → LinfZ) (nu : ℝ) (i : Fin 3) (x : (latticeFullData v nu).D) : ((latticeFullData v nu).advection i x : L2Z) = latticeAdvectionCLM v nu i (x : L2Z)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.latticeFullData_advection_apply`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.latticeFullData_advection_apply
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

theorem BookProof.NavierStokesFlow.FullEsa.latticeFullData_advection_apply (v : Fin 15 → LinfZ) (nu : ℝ) (i : Fin 3)
    (x : (latticeFullData v nu).D) :
    ((latticeFullData v nu).advection i x : L2Z) = latticeAdvectionCLM v nu i (x : L2Z) := by sorry
