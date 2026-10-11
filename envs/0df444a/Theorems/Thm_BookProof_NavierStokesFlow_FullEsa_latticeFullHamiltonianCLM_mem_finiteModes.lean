-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_latticeFullHamiltonianCLM_mem_finiteModes
-- name    : BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_mem_finiteModes
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T08:13:42.238006+00:00
-- url     : https://prove2.me/theorems/6e5f48c6-7a7d-4fb5-9593-e1b5e4821313
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_mem_finiteModes` (v : Fin 15 → LinfZ) (nu : ℝ) {f : L2Z} (hf : f ∈ finiteModes) : latticeFullHamiltonianCLM v nu f ∈ f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_mem_finiteModes` (v : Fin 15 → LinfZ) (nu : ℝ) {f : L2Z} (hf : f ∈ finiteModes) : latticeFullHamiltonianCLM v nu f ∈ finiteModes
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_mem_finiteModes`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_mem_finiteModes
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

theorem BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_mem_finiteModes (v : Fin 15 → LinfZ) (nu : ℝ)
    {f : L2Z} (hf : f ∈ finiteModes) : latticeFullHamiltonianCLM v nu f ∈ finiteModes := by sorry
