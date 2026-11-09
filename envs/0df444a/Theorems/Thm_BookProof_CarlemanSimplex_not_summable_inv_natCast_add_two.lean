-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_not_summable_inv_natCast_add_two
-- name    : BookProof.CarlemanSimplex.not_summable_inv_natCast_add_two
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:49:41.781639+00:00
-- url     : https://prove2.me/theorems/5a2fb522-f6dd-4011-9d47-8b9c2c958124
-- title:
--   `BookProof.CarlemanSimplex.not_summable_inv_natCast_add_two` : ¬ Summable (fun N : ℕ => ((N : ℝ) + 2)⁻¹)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.not_summable_inv_natCast_add_two` : ¬ Summable (fun N : ℕ => ((N : ℝ) + 2)⁻¹)
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.not_summable_inv_natCast_add_two`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.not_summable_inv_natCast_add_two
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Mathlib
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.CarlemanSimplex



open Finset
open BookProof.HermiteCarleman BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {u : (Fin d →₀ ℕ) → ℂ}
variable {lam : (Fin d →₀ ℕ) → ℝ} {w : Fin d → ℂ} {W M : Fin d → Fin d → ℂ} {z : ℂ}

theorem BookProof.CarlemanSimplex.not_summable_inv_natCast_add_two : ¬ Summable (fun N : ℕ => ((N : ℝ) + 2)⁻¹) := by sorry
