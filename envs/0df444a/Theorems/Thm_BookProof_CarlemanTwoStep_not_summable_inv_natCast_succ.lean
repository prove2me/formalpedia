-- Prove2me | Theorems.Thm_BookProof_CarlemanTwoStep_not_summable_inv_natCast_succ
-- name    : BookProof.CarlemanTwoStep.not_summable_inv_natCast_succ
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-07T22:52:44.514893+00:00
-- url     : https://prove2.me/theorems/2eac1739-1ce0-4bb9-8705-9d218a3d6db3
-- title:
--   `BookProof.CarlemanTwoStep.not_summable_inv_natCast_succ` : ¬ Summable (fun N : ℕ => ((N : ℝ) + 1)⁻¹)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanTwoStep`.
--
--   `BookProof.CarlemanTwoStep.not_summable_inv_natCast_succ` : ¬ Summable (fun N : ℕ => ((N : ℝ) + 1)⁻¹)
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanTwoStep.not_summable_inv_natCast_succ`.

-- Generated from ChapterCarlemanTwoStep.lean — theorem BookProof.CarlemanTwoStep.not_summable_inv_natCast_succ
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.CarlemanTwoStep



open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

variable {u : (Fin d →₀ ℕ) → ℂ}
variable {lam : (Fin d →₀ ℕ) → ℝ} {w1 w2 : Fin d → ℂ} {z : ℂ}

theorem BookProof.CarlemanTwoStep.not_summable_inv_natCast_succ : ¬ Summable (fun N : ℕ => ((N : ℝ) + 1)⁻¹) := by sorry
