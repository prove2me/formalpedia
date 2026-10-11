-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_diagFullData_hamiltonian
-- name    : BookProof.NavierStokesFlow.FullEsa.diagFullData_hamiltonian
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T08:32:04.112039+00:00
-- url     : https://prove2.me/theorems/bcbaa5a4-fd17-4b71-89e1-4d732d320cc4
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.diagFullData_hamiltonian` (c : Fin 15 → ℕ → ℝ) (p : Fin 3 → ℕ → ℝ) (nu : ℝ) : (diagFullData c p nu).hamiltonian = diagOp (diagFullSymbol c p nu)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.diagFullData_hamiltonian` (c : Fin 15 → ℕ → ℝ) (p : Fin 3 → ℕ → ℝ) (nu : ℝ) : (diagFullData c p nu).hamiltonian = diagOp (diagFullSymbol c p nu)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.diagFullData_hamiltonian`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.diagFullData_hamiltonian
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

theorem BookProof.NavierStokesFlow.FullEsa.diagFullData_hamiltonian (c : Fin 15 → ℕ → ℝ) (p : Fin 3 → ℕ → ℝ) (nu : ℝ) :
    (diagFullData c p nu).hamiltonian = diagOp (diagFullSymbol c p nu) := by sorry
