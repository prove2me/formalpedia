-- Prove2me | Theorems.Thm_BookProof_WallEsaSemibounded_wallHam_nonneg_form
-- name    : BookProof.WallEsaSemibounded.wallHam_nonneg_form
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:35:56.582785+00:00
-- url     : https://prove2.me/theorems/76943de6-30ea-46b1-9975-6e0f17c9bfc5
-- title:
--   The Lean 4 theorem `wallHam_nonneg_form` in the `ChapterWallEsaSemibounded` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `wallHam_nonneg_form` in the `ChapterWallEsaSemibounded` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterWallEsaSemibounded.lean

-- Generated from ChapterWallEsaSemibounded.lean — theorem BookProof.WallEsaSemibounded.wallHam_nonneg_form
import Mathlib
import Definitions.Def_ChapterWallEsaSemibounded
open BookProof.WallEsaSemibounded










open MeasureTheory SchwartzMap
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.ScalaronWallEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.WallEsaSemibounded.wallHam_nonneg_form (V : ℝ → ℝ)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hVnn : ∀ x, 0 ≤ V x) :
    SemiboundedBelowOn (ccDomain ℝ) (wallHam V hV) 0 := by sorry
