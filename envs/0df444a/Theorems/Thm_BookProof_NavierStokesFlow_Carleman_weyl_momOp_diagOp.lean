-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_Carleman_weyl_momOp_diagOp
-- name    : BookProof.NavierStokesFlow.Carleman.weyl_momOp_diagOp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:37:34.31898+00:00
-- url     : https://prove2.me/theorems/e0f14a55-8f61-406f-ae04-25063a595adb
-- title:
--   `BookProof.NavierStokesFlow.Carleman.weyl_momOp_diagOp` (a : ℕ → ℝ) : momOp.comp (diagOp a) + (diagOp a).comp momOp = tridiagOp (nsCoupling a)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCarleman`.
--
--   `BookProof.NavierStokesFlow.Carleman.weyl_momOp_diagOp` (a : ℕ → ℝ) : momOp.comp (diagOp a) + (diagOp a).comp momOp = tridiagOp (nsCoupling a)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.Carleman.weyl_momOp_diagOp`.

-- Generated from ChapterNavierStokesCarleman.lean — theorem BookProof.NavierStokesFlow.Carleman.weyl_momOp_diagOp
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman


open scoped ENNReal



open LpNat DiagonalEsa FullEsa

theorem BookProof.NavierStokesFlow.Carleman.weyl_momOp_diagOp (a : ℕ → ℝ) :
    momOp.comp (diagOp a) + (diagOp a).comp momOp = tridiagOp (nsCoupling a) := by sorry
