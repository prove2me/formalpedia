-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_diagUnboundedData_hamiltonian
-- name    : BookProof.NavierStokesFlow.FullEsa.diagUnboundedData_hamiltonian
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T08:14:47.747523+00:00
-- url     : https://prove2.me/theorems/7d4ff170-86a1-4650-b7e2-257f589f3bd2
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.diagUnboundedData_hamiltonian` : diagUnboundedData.hamiltonian = diagOp (fun n => -(2 * (n : ℝ)))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.diagUnboundedData_hamiltonian` : diagUnboundedData.hamiltonian = diagOp (fun n => -(2 * (n : ℝ)))
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.diagUnboundedData_hamiltonian`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.diagUnboundedData_hamiltonian
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.NavierStokesFlow.DiagonalEsa
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

theorem BookProof.NavierStokesFlow.FullEsa.diagUnboundedData_hamiltonian :
    diagUnboundedData.hamiltonian = diagOp (fun n => -(2 * (n : ℝ))) := by sorry
