-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_diagLagData_hFull
-- name    : BookProof.NavierStokesFlow.LagrangianEsa.diagLagData_hFull
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:20:38.265012+00:00
-- url     : https://prove2.me/theorems/8474f873-57de-4faa-a214-80c842dd4c91
-- title:
--   `BookProof.NavierStokesFlow.LagrangianEsa.diagLagData_hFull` (p q dr : Fin 3 → ℕ → ℝ) (c : ℕ → ℝ) (fr : Fin 3 → ℝ) {nu : ℝ} (hnu : 0 ≤ nu) : HasZeroDeficiencyOn (diagLagData...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesLagrangianEsa`.
--
--   `BookProof.NavierStokesFlow.LagrangianEsa.diagLagData_hFull` (p q dr : Fin 3 → ℕ → ℝ) (c : ℕ → ℝ) (fr : Fin 3 → ℝ) {nu : ℝ} (hnu : 0 ≤ nu) : HasZeroDeficiencyOn (diagLagData p q dr c fr hnu).D (diagLagData p q dr c fr hnu).hFull
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.LagrangianEsa.diagLagData_hFull`.

-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.diagLagData_hFull
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.BRSTNilpotent
open BookProof.ChapterF7
open BookProof.NavierStokesFlow.DiagonalEsa
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa




open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)
variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

theorem BookProof.NavierStokesFlow.LagrangianEsa.diagLagData_hFull (p q dr : Fin 3 → ℕ → ℝ) (c : ℕ → ℝ) (fr : Fin 3 → ℝ)
    {nu : ℝ} (hnu : 0 ≤ nu) :
    HasZeroDeficiencyOn (diagLagData p q dr c fr hnu).D (diagLagData p q dr c fr hnu).hFull := by sorry
