-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_Carleman_tridiagOp_basis_succ
-- name    : BookProof.NavierStokesFlow.Carleman.tridiagOp_basis_succ
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:35:54.611553+00:00
-- url     : https://prove2.me/theorems/42663038-8acd-42a0-8a13-09e667672406
-- title:
--   `BookProof.NavierStokesFlow.Carleman.tridiagOp_basis_succ` (c : ℕ → ℂ) (k : ℕ) : ((tridiagOp c (basis (k + 1)) : lpFiniteModes ℕ) : L2N) = (starRingEnd ℂ (c (k + 1))) • lp.single 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCarleman`.
--
--   `BookProof.NavierStokesFlow.Carleman.tridiagOp_basis_succ` (c : ℕ → ℂ) (k : ℕ) : ((tridiagOp c (basis (k + 1)) : lpFiniteModes ℕ) : L2N) = (starRingEnd ℂ (c (k + 1))) • lp.single 2 (k + 2) (1 : ℂ) + (c k) • lp.single 2 k (1 : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.Carleman.tridiagOp_basis_succ`.

-- Generated from ChapterNavierStokesCarleman.lean — theorem BookProof.NavierStokesFlow.Carleman.tridiagOp_basis_succ
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

theorem BookProof.NavierStokesFlow.Carleman.tridiagOp_basis_succ (c : ℕ → ℂ) (k : ℕ) :
    ((tridiagOp c (basis (k + 1)) : lpFiniteModes ℕ) : L2N)
      = (starRingEnd ℂ (c (k + 1))) • lp.single 2 (k + 2) (1 : ℂ)
        + (c k) • lp.single 2 k (1 : ℂ) := by sorry
