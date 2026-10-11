-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_jacobiFullData_hamiltonian
-- name    : BookProof.NavierStokesFlow.FullEsa.jacobiFullData_hamiltonian
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T08:14:54.535978+00:00
-- url     : https://prove2.me/theorems/28a8ce83-2ed0-4b29-8a9f-19479675ccf3
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.jacobiFullData_hamiltonian` : jacobiFullData.hamiltonian = jacobiOp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.jacobiFullData_hamiltonian` : jacobiFullData.hamiltonian = jacobiOp
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.jacobiFullData_hamiltonian`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.jacobiFullData_hamiltonian
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.DiagonalEsa
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

theorem BookProof.NavierStokesFlow.FullEsa.jacobiFullData_hamiltonian : jacobiFullData.hamiltonian = jacobiOp := by sorry
