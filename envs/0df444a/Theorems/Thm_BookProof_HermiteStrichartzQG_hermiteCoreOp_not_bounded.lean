-- Prove2me | Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteCoreOp_not_bounded
-- name    : BookProof.HermiteStrichartzQG.hermiteCoreOp_not_bounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:48:21.803986+00:00
-- url     : https://prove2.me/theorems/e88bd29a-989a-4e86-b8df-6b0812b06d2f
-- title:
--   `BookProof.HermiteStrichartzQG.hermiteCoreOp_not_bounded` (lam : ℕ → ℝ) (hlam : ∀ C : ℝ, ∃ n, C < |lam n|) : ¬ ∃ C : ℝ, ∀ f : hermiteCore, ‖hermiteCoreOp lam f‖ ≤ C *...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStrichartzHermiteQG`.
--
--   `BookProof.HermiteStrichartzQG.hermiteCoreOp_not_bounded` (lam : ℕ → ℝ) (hlam : ∀ C : ℝ, ∃ n, C < |lam n|) : ¬ ∃ C : ℝ, ∀ f : hermiteCore, ‖hermiteCoreOp lam f‖ ≤ C * ‖(f : L2R)‖
--
--   Formalization note: Lean 4 identifier `BookProof.HermiteStrichartzQG.hermiteCoreOp_not_bounded`.

-- Generated from ChapterStrichartzHermiteQG.lean — theorem BookProof.HermiteStrichartzQG.hermiteCoreOp_not_bounded
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore
open BookProof.HermiteStrichartzQG



open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

theorem BookProof.HermiteStrichartzQG.hermiteCoreOp_not_bounded (lam : ℕ → ℝ) (hlam : ∀ C : ℝ, ∃ n, C < |lam n|) :
    ¬ ∃ C : ℝ, ∀ f : hermiteCore, ‖hermiteCoreOp lam f‖ ≤ C * ‖(f : L2R)‖ := by sorry
