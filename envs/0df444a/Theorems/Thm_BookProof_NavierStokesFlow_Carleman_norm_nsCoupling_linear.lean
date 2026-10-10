-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_Carleman_norm_nsCoupling_linear
-- name    : BookProof.NavierStokesFlow.Carleman.norm_nsCoupling_linear
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:39:05.990013+00:00
-- url     : https://prove2.me/theorems/f66f589d-a8cb-4dc4-bee7-7a945de54f7f
-- title:
--   `BookProof.NavierStokesFlow.Carleman.norm_nsCoupling_linear` (n : ℕ) : ‖nsCoupling (fun m : ℕ => (m : ℝ) + 1) n‖ = ((n : ℝ) + 3 / 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCarleman`.
--
--   `BookProof.NavierStokesFlow.Carleman.norm_nsCoupling_linear` (n : ℕ) : ‖nsCoupling (fun m : ℕ => (m : ℝ) + 1) n‖ = ((n : ℝ) + 3 / 2)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.Carleman.norm_nsCoupling_linear`.

-- Generated from ChapterNavierStokesCarleman.lean — theorem BookProof.NavierStokesFlow.Carleman.norm_nsCoupling_linear
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman


open scoped ENNReal



open LpNat DiagonalEsa FullEsa

theorem BookProof.NavierStokesFlow.Carleman.norm_nsCoupling_linear (n : ℕ) :
    ‖nsCoupling (fun m : ℕ => (m : ℝ) + 1) n‖ = ((n : ℝ) + 3 / 2) := by sorry
