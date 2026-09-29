-- Prove2me | Theorems.Thm_BookProof_WallEsaSemibounded_opCc_quadratic_form
-- name    : BookProof.WallEsaSemibounded.opCc_quadratic_form
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T13:21:35.64821+00:00
-- url     : https://prove2.me/theorems/c86d6643-2f17-451b-9c23-22ed3af2980a
-- title:
--   The Lean 4 theorem `opCc_quadratic_form` in the `ChapterWallEsaSemibounded` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `opCc_quadratic_form` in the `ChapterWallEsaSemibounded` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterWallEsaSemibounded.lean

-- Generated from ChapterWallEsaSemibounded.lean — theorem BookProof.WallEsaSemibounded.opCc_quadratic_form
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

theorem BookProof.WallEsaSemibounded.opCc_quadratic_form (V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (f : ccSchwartz ℝ) :
    (inner ℂ (opCc V hV (ccEquiv ℝ f))
        ((ccEquiv ℝ f : ccDomain ℝ) : Lp ℂ 2 (volume : Measure ℝ)) : ℂ)
      = ((∫ x, V x * ‖(f : 𝓢(ℝ, ℂ)) x‖ ^ 2 : ℝ) : ℂ) := by sorry
