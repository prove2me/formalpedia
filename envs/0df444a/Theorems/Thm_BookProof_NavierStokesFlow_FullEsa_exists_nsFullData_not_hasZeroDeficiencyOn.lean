-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_exists_nsFullData_not_hasZeroDeficiencyOn
-- name    : BookProof.NavierStokesFlow.FullEsa.exists_nsFullData_not_hasZeroDeficiencyOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T08:14:36.145525+00:00
-- url     : https://prove2.me/theorems/1e285a64-c3df-4ab7-a831-10f517840ba0
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.exists_nsFullData_not_hasZeroDeficiencyOn` : ∃ d : NSFullData L2N, ¬ HasZeroDeficiencyOn d.D d.hamiltonian
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.exists_nsFullData_not_hasZeroDeficiencyOn` : ∃ d : NSFullData L2N, ¬ HasZeroDeficiencyOn d.D d.hamiltonian
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.exists_nsFullData_not_hasZeroDeficiencyOn`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.exists_nsFullData_not_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow.DiagonalEsa
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

theorem BookProof.NavierStokesFlow.FullEsa.exists_nsFullData_not_hasZeroDeficiencyOn :
    ∃ d : NSFullData L2N, ¬ HasZeroDeficiencyOn d.D d.hamiltonian := by sorry
