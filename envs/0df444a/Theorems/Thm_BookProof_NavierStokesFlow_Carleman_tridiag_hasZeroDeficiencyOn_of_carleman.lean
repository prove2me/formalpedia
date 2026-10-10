-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_Carleman_tridiag_hasZeroDeficiencyOn_of_carleman
-- name    : BookProof.NavierStokesFlow.Carleman.tridiag_hasZeroDeficiencyOn_of_carleman
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:37:43.676566+00:00
-- url     : https://prove2.me/theorems/0a3267f0-834f-4fdc-857b-459b147dbb29
-- title:
--   `BookProof.NavierStokesFlow.Carleman.tridiag_hasZeroDeficiencyOn_of_carleman` (c : ℕ → ℂ) (hcar : ¬ Summable fun n => 1 / ‖c n‖) : HasZeroDeficiencyOn (lpFiniteModes ℕ) (tridiagOp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCarleman`.
--
--   `BookProof.NavierStokesFlow.Carleman.tridiag_hasZeroDeficiencyOn_of_carleman` (c : ℕ → ℂ) (hcar : ¬ Summable fun n => 1 / ‖c n‖) : HasZeroDeficiencyOn (lpFiniteModes ℕ) (tridiagOp c)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.Carleman.tridiag_hasZeroDeficiencyOn_of_carleman`.

-- Generated from ChapterNavierStokesCarleman.lean — theorem BookProof.NavierStokesFlow.Carleman.tridiag_hasZeroDeficiencyOn_of_carleman
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman


open scoped ENNReal



open LpNat DiagonalEsa FullEsa

theorem BookProof.NavierStokesFlow.Carleman.tridiag_hasZeroDeficiencyOn_of_carleman (c : ℕ → ℂ)
    (hcar : ¬ Summable fun n => 1 / ‖c n‖) :
    HasZeroDeficiencyOn (lpFiniteModes ℕ) (tridiagOp c) := by sorry
