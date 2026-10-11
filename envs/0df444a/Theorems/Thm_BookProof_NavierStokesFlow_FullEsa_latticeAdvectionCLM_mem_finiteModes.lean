-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_latticeAdvectionCLM_mem_finiteModes
-- name    : BookProof.NavierStokesFlow.FullEsa.latticeAdvectionCLM_mem_finiteModes
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T08:13:41.284655+00:00
-- url     : https://prove2.me/theorems/fec57120-51f7-41e8-98f1-66213caeed20
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.latticeAdvectionCLM_mem_finiteModes` (v : Fin 15 → LinfZ) (nu : ℝ) (i : Fin 3) {f : L2Z} (hf : f ∈ finiteModes) : latticeAdvectionCLM v nu i f ∈
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.latticeAdvectionCLM_mem_finiteModes` (v : Fin 15 → LinfZ) (nu : ℝ) (i : Fin 3) {f : L2Z} (hf : f ∈ finiteModes) : latticeAdvectionCLM v nu i f ∈ finiteModes
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.latticeAdvectionCLM_mem_finiteModes`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.latticeAdvectionCLM_mem_finiteModes
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesEsa
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

theorem BookProof.NavierStokesFlow.FullEsa.latticeAdvectionCLM_mem_finiteModes (v : Fin 15 → LinfZ) (nu : ℝ) (i : Fin 3)
    {f : L2Z} (hf : f ∈ finiteModes) : latticeAdvectionCLM v nu i f ∈ finiteModes := by sorry
