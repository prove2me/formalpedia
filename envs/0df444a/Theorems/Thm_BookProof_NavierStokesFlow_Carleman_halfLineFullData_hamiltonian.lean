-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_Carleman_halfLineFullData_hamiltonian
-- name    : BookProof.NavierStokesFlow.Carleman.halfLineFullData_hamiltonian
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:37:07.8621+00:00
-- url     : https://prove2.me/theorems/eda38796-3fea-436d-ab14-ee2915331928
-- title:
--   `BookProof.NavierStokesFlow.Carleman.halfLineFullData_hamiltonian` (c : Fin 15 → ℕ → ℝ) (nu : ℝ) : (halfLineFullData c nu).hamiltonian = tridiagOp (nsCoupling (halfLineSymbol c nu)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCarleman`.
--
--   `BookProof.NavierStokesFlow.Carleman.halfLineFullData_hamiltonian` (c : Fin 15 → ℕ → ℝ) (nu : ℝ) : (halfLineFullData c nu).hamiltonian = tridiagOp (nsCoupling (halfLineSymbol c nu))
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.Carleman.halfLineFullData_hamiltonian`.

-- Generated from ChapterNavierStokesCarleman.lean — theorem BookProof.NavierStokesFlow.Carleman.halfLineFullData_hamiltonian
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman


open scoped ENNReal



open LpNat DiagonalEsa FullEsa

theorem BookProof.NavierStokesFlow.Carleman.halfLineFullData_hamiltonian (c : Fin 15 → ℕ → ℝ) (nu : ℝ) :
    (halfLineFullData c nu).hamiltonian = tridiagOp (nsCoupling (halfLineSymbol c nu)) := by sorry
