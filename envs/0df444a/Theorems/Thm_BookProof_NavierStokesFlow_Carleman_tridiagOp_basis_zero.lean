-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_Carleman_tridiagOp_basis_zero
-- name    : BookProof.NavierStokesFlow.Carleman.tridiagOp_basis_zero
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:36:42.716467+00:00
-- url     : https://prove2.me/theorems/fe819ef7-9560-4cea-b969-2af883ee8337
-- title:
--   `BookProof.NavierStokesFlow.Carleman.tridiagOp_basis_zero` (c : ℕ → ℂ) : ((tridiagOp c (basis 0) : lpFiniteModes ℕ) : L2N) = (starRingEnd ℂ (c 0)) • lp.single 2 1 (1 : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCarleman`.
--
--   `BookProof.NavierStokesFlow.Carleman.tridiagOp_basis_zero` (c : ℕ → ℂ) : ((tridiagOp c (basis 0) : lpFiniteModes ℕ) : L2N) = (starRingEnd ℂ (c 0)) • lp.single 2 1 (1 : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.Carleman.tridiagOp_basis_zero`.

-- Generated from ChapterNavierStokesCarleman.lean — theorem BookProof.NavierStokesFlow.Carleman.tridiagOp_basis_zero
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman


open scoped ENNReal



open LpNat DiagonalEsa FullEsa

theorem BookProof.NavierStokesFlow.Carleman.tridiagOp_basis_zero (c : ℕ → ℂ) :
    ((tridiagOp c (basis 0) : lpFiniteModes ℕ) : L2N)
      = (starRingEnd ℂ (c 0)) • lp.single 2 1 (1 : ℂ) := by sorry
