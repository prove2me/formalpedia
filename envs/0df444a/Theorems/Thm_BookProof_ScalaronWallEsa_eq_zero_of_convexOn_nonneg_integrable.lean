-- Prove2me | Theorems.Thm_BookProof_ScalaronWallEsa_eq_zero_of_convexOn_nonneg_integrable
-- name    : BookProof.ScalaronWallEsa.eq_zero_of_convexOn_nonneg_integrable
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:37:27.656973+00:00
-- url     : https://prove2.me/theorems/a8071f42-58ec-44db-b54a-72b55cbc42ad
-- title:
--   The Lean 4 theorem `eq_zero_of_convexOn_nonneg_integrable` in the `ChapterScalaronWallEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `eq_zero_of_convexOn_nonneg_integrable` in the `ChapterScalaronWallEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronWallEsa.lean

-- Generated from ChapterScalaronWallEsa.lean — theorem BookProof.ScalaronWallEsa.eq_zero_of_convexOn_nonneg_integrable
import Mathlib
import Definitions.Def_ChapterScalaronWallEsa
open BookProof.ScalaronWallEsa












open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.Starobinsky BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent
open BookProof.WeakSecondDeriv

noncomputable section

theorem BookProof.ScalaronWallEsa.eq_zero_of_convexOn_nonneg_integrable {F : ℝ → ℝ} (hconv : ConvexOn ℝ univ F)
    (hnn : ∀ x, 0 ≤ F x) (hint : Integrable F volume) (a : ℝ) : F a = 0 := by sorry
