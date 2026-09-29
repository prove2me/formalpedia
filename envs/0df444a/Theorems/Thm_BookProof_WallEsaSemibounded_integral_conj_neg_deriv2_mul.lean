-- Prove2me | Theorems.Thm_BookProof_WallEsaSemibounded_integral_conj_neg_deriv2_mul
-- name    : BookProof.WallEsaSemibounded.integral_conj_neg_deriv2_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T13:21:21.412333+00:00
-- url     : https://prove2.me/theorems/67823146-e348-4c7a-b534-02f676b98b5f
-- title:
--   The Lean 4 theorem `integral_conj_neg_deriv2_mul` in the `ChapterWallEsaSemibounded` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `integral_conj_neg_deriv2_mul` in the `ChapterWallEsaSemibounded` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterWallEsaSemibounded.lean

-- Generated from ChapterWallEsaSemibounded.lean — theorem BookProof.WallEsaSemibounded.integral_conj_neg_deriv2_mul
import Mathlib
import Definitions.Def_ChapterWallEsaSemibounded
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStrichartzWave
open BookProof.WallEsaSemibounded










open MeasureTheory SchwartzMap
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.ScalaronWallEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.WallEsaSemibounded.integral_conj_neg_deriv2_mul (f : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    ∫ x, (starRingEnd ℂ) (-deriv (deriv f) x) * f x = ((∫ x, ‖deriv f x‖ ^ 2 : ℝ) : ℂ) := by sorry
