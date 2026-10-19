-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_latticeFullHamiltonianCLM_isSelfAdjoint
-- name    : BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_isSelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T08:13:04.76202+00:00
-- url     : https://prove2.me/theorems/a3c58d90-cb01-4ed1-8214-0bf8d1d06bcc
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_isSelfAdjoint` (v : Fin 15 → LinfZ) (nu : ℝ) : IsSelfAdjoint (latticeFullHamiltonianCLM v nu)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_isSelfAdjoint` (v : Fin 15 → LinfZ) (nu : ℝ) : IsSelfAdjoint (latticeFullHamiltonianCLM v nu)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_isSelfAdjoint`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_isSelfAdjoint
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

theorem BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_isSelfAdjoint (v : Fin 15 → LinfZ) (nu : ℝ) :
    IsSelfAdjoint (latticeFullHamiltonianCLM v nu) := by sorry
