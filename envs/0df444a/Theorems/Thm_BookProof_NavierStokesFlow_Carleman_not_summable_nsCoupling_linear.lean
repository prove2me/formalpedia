-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_Carleman_not_summable_nsCoupling_linear
-- name    : BookProof.NavierStokesFlow.Carleman.not_summable_nsCoupling_linear
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:39:36.178567+00:00
-- url     : https://prove2.me/theorems/8ca7cbd6-e21b-4f9a-8dfd-86c1704d2fe3
-- title:
--   `BookProof.NavierStokesFlow.Carleman.not_summable_nsCoupling_linear` : ¬ Summable fun n : ℕ => 1 / ‖nsCoupling (fun m : ℕ => (m : ℝ) + 1) n‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCarleman`.
--
--   `BookProof.NavierStokesFlow.Carleman.not_summable_nsCoupling_linear` : ¬ Summable fun n : ℕ => 1 / ‖nsCoupling (fun m : ℕ => (m : ℝ) + 1) n‖
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.Carleman.not_summable_nsCoupling_linear`.

-- Generated from ChapterNavierStokesCarleman.lean — theorem BookProof.NavierStokesFlow.Carleman.not_summable_nsCoupling_linear
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman


open scoped ENNReal



open LpNat DiagonalEsa FullEsa

theorem BookProof.NavierStokesFlow.Carleman.not_summable_nsCoupling_linear :
    ¬ Summable fun n : ℕ => 1 / ‖nsCoupling (fun m : ℕ => (m : ℝ) + 1) n‖ := by sorry
