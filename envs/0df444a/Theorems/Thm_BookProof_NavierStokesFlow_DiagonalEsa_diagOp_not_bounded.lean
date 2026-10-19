-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiagonalEsa_diagOp_not_bounded
-- name    : BookProof.NavierStokesFlow.DiagonalEsa.diagOp_not_bounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:17:39.616252+00:00
-- url     : https://prove2.me/theorems/2e724cc3-7220-464e-8d7f-aa74897ef34e
-- title:
--   `BookProof.NavierStokesFlow.DiagonalEsa.diagOp_not_bounded` (c : ℕ → ℝ) (hc : ∀ C : ℝ, ∃ n, C < |c n|) : ¬ ∃ C : ℝ, ∀ f : lpFiniteModes ℕ, ‖diagOp c f‖ ≤ C * ‖f‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesDeficiency`.
--
--   `BookProof.NavierStokesFlow.DiagonalEsa.diagOp_not_bounded` (c : ℕ → ℝ) (hc : ∀ C : ℝ, ∃ n, C < |c n|) : ¬ ∃ C : ℝ, ∀ f : lpFiniteModes ℕ, ‖diagOp c f‖ ≤ C * ‖f‖
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.DiagonalEsa.diagOp_not_bounded`.

-- Generated from ChapterNavierStokesDeficiency.lean — theorem BookProof.NavierStokesFlow.DiagonalEsa.diagOp_not_bounded
import Mathlib
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.DiagonalEsa


open scoped ENNReal

theorem BookProof.NavierStokesFlow.DiagonalEsa.diagOp_not_bounded (c : ℕ → ℝ) (hc : ∀ C : ℝ, ∃ n, C < |c n|) :
    ¬ ∃ C : ℝ, ∀ f : lpFiniteModes ℕ, ‖diagOp c f‖ ≤ C * ‖f‖ := by sorry
