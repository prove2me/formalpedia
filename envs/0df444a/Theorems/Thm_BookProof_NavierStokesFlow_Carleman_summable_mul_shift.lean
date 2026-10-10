-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_Carleman_summable_mul_shift
-- name    : BookProof.NavierStokesFlow.Carleman.summable_mul_shift
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:36:35.831348+00:00
-- url     : https://prove2.me/theorems/16572e59-193a-45c7-843d-54bdfebbf3fa
-- title:
--   `BookProof.NavierStokesFlow.Carleman.summable_mul_shift` (w : L2N) : Summable fun n : ℕ => ‖(w : ℕ → ℂ) n‖ * ‖(w : ℕ → ℂ) (n + 1)‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCarleman`.
--
--   `BookProof.NavierStokesFlow.Carleman.summable_mul_shift` (w : L2N) : Summable fun n : ℕ => ‖(w : ℕ → ℂ) n‖ * ‖(w : ℕ → ℂ) (n + 1)‖
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.Carleman.summable_mul_shift`.

-- Generated from ChapterNavierStokesCarleman.lean — theorem BookProof.NavierStokesFlow.Carleman.summable_mul_shift
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman


open scoped ENNReal



open LpNat DiagonalEsa FullEsa

theorem BookProof.NavierStokesFlow.Carleman.summable_mul_shift (w : L2N) :
    Summable fun n : ℕ => ‖(w : ℕ → ℂ) n‖ * ‖(w : ℕ → ℂ) (n + 1)‖ := by sorry
