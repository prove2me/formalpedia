-- Prove2me | Theorems.Thm_BookProof_WallEsaSemibounded_ccEquiv_norm_sq
-- name    : BookProof.WallEsaSemibounded.ccEquiv_norm_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:17:14.515978+00:00
-- url     : https://prove2.me/theorems/32036ffa-312c-4ce4-81e1-dd05967e8297
-- title:
--   The Lean 4 theorem `ccEquiv_norm_sq` in the `ChapterWallEsaSemibounded` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ccEquiv_norm_sq` in the `ChapterWallEsaSemibounded` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterWallEsaSemibounded.lean

-- Generated from ChapterWallEsaSemibounded.lean — theorem BookProof.WallEsaSemibounded.ccEquiv_norm_sq
import Mathlib
import Definitions.Def_ChapterWallEsaSemibounded
open BookProof.WallEsaSemibounded










open MeasureTheory SchwartzMap
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.ScalaronWallEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.WallEsaSemibounded.ccEquiv_norm_sq (f : ccSchwartz ℝ) :
    ‖((ccEquiv ℝ f : ccDomain ℝ) : Lp ℂ 2 (volume : Measure ℝ))‖ ^ 2
      = ∫ x, ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 := by sorry
