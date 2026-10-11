-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_latticeFullHamiltonianCLM_isSymmetric
-- name    : BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_isSymmetric
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T08:13:14.541277+00:00
-- url     : https://prove2.me/theorems/8456270e-a230-4b51-bd14-25b0f315a3de
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_isSymmetric` (v : Fin 15 → LinfZ) (nu : ℝ) : ((latticeFullHamiltonianCLM v nu : L2Z →L[ℂ] L2Z) : L2Z →ₗ[ℂ] L2Z).IsSymm
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_isSymmetric` (v : Fin 15 → LinfZ) (nu : ℝ) : ((latticeFullHamiltonianCLM v nu : L2Z →L[ℂ] L2Z) : L2Z →ₗ[ℂ] L2Z).IsSymmetric
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_isSymmetric`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_isSymmetric
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

theorem BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_isSymmetric (v : Fin 15 → LinfZ) (nu : ℝ) :
    ((latticeFullHamiltonianCLM v nu : L2Z →L[ℂ] L2Z) : L2Z →ₗ[ℂ] L2Z).IsSymmetric := by sorry
