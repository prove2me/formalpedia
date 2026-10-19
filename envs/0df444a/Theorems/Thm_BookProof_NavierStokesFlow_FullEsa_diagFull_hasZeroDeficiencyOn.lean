-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_diagFull_hasZeroDeficiencyOn
-- name    : BookProof.NavierStokesFlow.FullEsa.diagFull_hasZeroDeficiencyOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:04:34.072579+00:00
-- url     : https://prove2.me/theorems/c7fa56d5-5de3-4255-874f-217a15e84b81
-- title:
--   `BookProof.NavierStokesFlow.FullEsa.diagFull_hasZeroDeficiencyOn` (c : Fin 15 → ℕ → ℝ) (p : Fin 3 → ℕ → ℝ) (nu : ℝ) : HasZeroDeficiencyOn (diagFullData c p nu).D (diagFullData c p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullEsa`.
--
--   `BookProof.NavierStokesFlow.FullEsa.diagFull_hasZeroDeficiencyOn` (c : Fin 15 → ℕ → ℝ) (p : Fin 3 → ℕ → ℝ) (nu : ℝ) : HasZeroDeficiencyOn (diagFullData c p nu).D (diagFullData c p nu).hamiltonian
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FullEsa.diagFull_hasZeroDeficiencyOn`.

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.diagFull_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterNavierStokesDeficiency
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

theorem BookProof.NavierStokesFlow.FullEsa.diagFull_hasZeroDeficiencyOn (c : Fin 15 → ℕ → ℝ) (p : Fin 3 → ℕ → ℝ) (nu : ℝ) :
    HasZeroDeficiencyOn (diagFullData c p nu).D (diagFullData c p nu).hamiltonian := by sorry
