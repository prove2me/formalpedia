-- Prove2me | Theorems.Thm_BookProof_WallEsaSemibounded_kinCcR_quadratic_form
-- name    : BookProof.WallEsaSemibounded.kinCcR_quadratic_form
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T13:21:49.996331+00:00
-- url     : https://prove2.me/theorems/94c5e0e1-6a9e-44ba-b334-a10857e6560e
-- title:
--   The Lean 4 theorem `kinCcR_quadratic_form` in the `ChapterWallEsaSemibounded` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `kinCcR_quadratic_form` in the `ChapterWallEsaSemibounded` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterWallEsaSemibounded.lean

-- Generated from ChapterWallEsaSemibounded.lean — theorem BookProof.WallEsaSemibounded.kinCcR_quadratic_form
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

theorem BookProof.WallEsaSemibounded.kinCcR_quadratic_form (f : ccSchwartz ℝ) :
    (inner ℂ (kinCcR (ccEquiv ℝ f))
        ((ccEquiv ℝ f : ccDomain ℝ) : Lp ℂ 2 (volume : Measure ℝ)) : ℂ)
      = ((∫ x, ‖deriv ((f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by sorry
