-- Prove2me | Theorems.Thm_BookProof_WallEsaSemibounded_inner_toLp_self
-- name    : BookProof.WallEsaSemibounded.inner_toLp_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:17:03.26253+00:00
-- url     : https://prove2.me/theorems/6236a96a-8260-4ba4-ae90-d448b931c967
-- title:
--   The Lean 4 theorem `inner_toLp_self` in the `ChapterWallEsaSemibounded` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `inner_toLp_self` in the `ChapterWallEsaSemibounded` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterWallEsaSemibounded.lean

-- Generated from ChapterWallEsaSemibounded.lean — theorem BookProof.WallEsaSemibounded.inner_toLp_self
import Mathlib
import Definitions.Def_ChapterWallEsaSemibounded
open BookProof.WallEsaSemibounded










open MeasureTheory SchwartzMap
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.ScalaronWallEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.WallEsaSemibounded.inner_toLp_self (g : 𝓢(ℝ, ℂ)) :
    (inner ℂ (g.toLp 2 (volume : Measure ℝ)) (g.toLp 2 (volume : Measure ℝ)) : ℂ)
      = ((∫ x, ‖g x‖ ^ 2 : ℝ) : ℂ) := by sorry
