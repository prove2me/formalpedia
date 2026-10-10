-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_Carleman_summable_normSq
-- name    : BookProof.NavierStokesFlow.Carleman.summable_normSq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T16:50:51.866817+00:00
-- url     : https://prove2.me/theorems/0715d731-d7be-4397-8dce-d95e38dbf4cb
-- title:
--   `BookProof.NavierStokesFlow.Carleman.summable_normSq` (f : L2N) : Summable fun n : ℕ => ‖(f : ℕ → ℂ) n‖ ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCarleman`.
--
--   `BookProof.NavierStokesFlow.Carleman.summable_normSq` (f : L2N) : Summable fun n : ℕ => ‖(f : ℕ → ℂ) n‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.Carleman.summable_normSq`.

-- Generated from ChapterNavierStokesCarleman.lean — theorem BookProof.NavierStokesFlow.Carleman.summable_normSq
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman


open scoped ENNReal



open LpNat DiagonalEsa FullEsa

theorem BookProof.NavierStokesFlow.Carleman.summable_normSq (f : L2N) : Summable fun n : ℕ => ‖(f : ℕ → ℂ) n‖ ^ 2 := by sorry
