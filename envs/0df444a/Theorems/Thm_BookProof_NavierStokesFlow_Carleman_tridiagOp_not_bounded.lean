-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_Carleman_tridiagOp_not_bounded
-- name    : BookProof.NavierStokesFlow.Carleman.tridiagOp_not_bounded
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:37:51.020975+00:00
-- url     : https://prove2.me/theorems/325d7df0-61e8-44ea-8357-64e080368277
-- title:
--   `BookProof.NavierStokesFlow.Carleman.tridiagOp_not_bounded` (c : ℕ → ℂ) (hc : ∀ C : ℝ, ∃ n, C < ‖c n‖) : ¬ ∃ C : ℝ, ∀ f : lpFiniteModes ℕ, ‖tridiagOp c f‖ ≤ C * ‖f‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCarleman`.
--
--   `BookProof.NavierStokesFlow.Carleman.tridiagOp_not_bounded` (c : ℕ → ℂ) (hc : ∀ C : ℝ, ∃ n, C < ‖c n‖) : ¬ ∃ C : ℝ, ∀ f : lpFiniteModes ℕ, ‖tridiagOp c f‖ ≤ C * ‖f‖
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.Carleman.tridiagOp_not_bounded`.

-- Generated from ChapterNavierStokesCarleman.lean — theorem BookProof.NavierStokesFlow.Carleman.tridiagOp_not_bounded
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

theorem BookProof.NavierStokesFlow.Carleman.tridiagOp_not_bounded (c : ℕ → ℂ) (hc : ∀ C : ℝ, ∃ n, C < ‖c n‖) :
    ¬ ∃ C : ℝ, ∀ f : lpFiniteModes ℕ, ‖tridiagOp c f‖ ≤ C * ‖f‖ := by sorry
