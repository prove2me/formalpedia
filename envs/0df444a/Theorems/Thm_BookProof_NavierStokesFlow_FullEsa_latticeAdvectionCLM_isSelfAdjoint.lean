-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_latticeAdvectionCLM_isSelfAdjoint
-- name    : BookProof.NavierStokesFlow.FullEsa.latticeAdvectionCLM_isSelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T08:31:56.20432+00:00
-- url     : https://prove2.me/theorems/917e383d-5186-46a7-926b-ac5aed35ab9a
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.latticeAdvectionCLM_isSelfAdjoint` (v : Fin 15 → LinfZ) (nu : ℝ) (i : Fin 3) : IsSelfAdjoint (latticeAdvectionCLM v nu i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.latticeAdvectionCLM_isSelfAdjoint` (v : Fin 15 → LinfZ) (nu : ℝ) (i : Fin 3) : IsSelfAdjoint (latticeAdvectionCLM v nu i)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.latticeAdvectionCLM_isSelfAdjoint`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.latticeAdvectionCLM_isSelfAdjoint
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

theorem BookProof.NavierStokesFlow.FullEsa.latticeAdvectionCLM_isSelfAdjoint (v : Fin 15 → LinfZ) (nu : ℝ) (i : Fin 3) :
    IsSelfAdjoint (latticeAdvectionCLM v nu i) := by sorry
