-- Prove2me | Theorems.Thm_BookProof_CarlemanSimplex_ladderQ_eq_zero
-- name    : BookProof.CarlemanSimplex.ladderQ_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-07T22:49:36.123739+00:00
-- url     : https://prove2.me/theorems/9c3e7afe-e731-4fa8-93d6-17a56c75e40c
-- title:
--   `BookProof.CarlemanSimplex.ladderQ_eq_zero` {B : ℝ} (hz : z.im ≠ 0) (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (hM : ∀ i j, M j i = (starRingEnd ℂ) (M i...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanSimplex`.
--
--   `BookProof.CarlemanSimplex.ladderQ_eq_zero` {B : ℝ} (hz : z.im ≠ 0) (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (hM : ∀ i j, M j i = (starRingEnd ℂ) (M i j)) (hrec : LadderRecQ u lam w W M z) : ∀ a, u a = 0
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanSimplex.ladderQ_eq_zero`.

-- Generated from ChapterCarlemanSimplex.lean — theorem BookProof.CarlemanSimplex.ladderQ_eq_zero
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

theorem BookProof.CarlemanSimplex.ladderQ_eq_zero {B : ℝ} (hz : z.im ≠ 0)
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B)
    (hM : ∀ i j, M j i = (starRingEnd ℂ) (M i j))
    (hrec : LadderRecQ u lam w W M z) : ∀ a, u a = 0 := by sorry
