-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_latticeFull_hasZeroDeficiencyOn
-- name    : BookProof.NavierStokesFlow.FullEsa.latticeFull_hasZeroDeficiencyOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T08:14:26.892675+00:00
-- url     : https://prove2.me/theorems/9b49cad2-a469-40bf-8ff7-e31168ed41a5
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.latticeFull_hasZeroDeficiencyOn` (v : Fin 15 → LinfZ) (nu : ℝ) : HasZeroDeficiencyOn (latticeFullData v nu).D (latticeFullData v nu).hamiltonian
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.latticeFull_hasZeroDeficiencyOn` (v : Fin 15 → LinfZ) (nu : ℝ) : HasZeroDeficiencyOn (latticeFullData v nu).D (latticeFullData v nu).hamiltonian
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.latticeFull_hasZeroDeficiencyOn`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.latticeFull_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

theorem BookProof.NavierStokesFlow.FullEsa.latticeFull_hasZeroDeficiencyOn (v : Fin 15 → LinfZ) (nu : ℝ) :
    HasZeroDeficiencyOn (latticeFullData v nu).D (latticeFullData v nu).hamiltonian := by sorry
