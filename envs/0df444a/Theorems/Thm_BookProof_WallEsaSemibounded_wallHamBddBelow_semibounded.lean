-- Prove2me | Theorems.Thm_BookProof_WallEsaSemibounded_wallHamBddBelow_semibounded
-- name    : BookProof.WallEsaSemibounded.wallHamBddBelow_semibounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:17:15.550983+00:00
-- url     : https://prove2.me/theorems/df8375e0-b5eb-42b6-83ac-efefad815ad2
-- title:
--   The Lean 4 theorem `wallHamBddBelow_semibounded` in the `ChapterWallEsaSemibounded` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `wallHamBddBelow_semibounded` in the `ChapterWallEsaSemibounded` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterWallEsaSemibounded.lean

-- Generated from ChapterWallEsaSemibounded.lean — theorem BookProof.WallEsaSemibounded.wallHamBddBelow_semibounded
import Mathlib
import Definitions.Def_ChapterWallEsaSemibounded
open BookProof.WallEsaSemibounded










open MeasureTheory SchwartzMap
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.ScalaronWallEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.WallEsaSemibounded.wallHamBddBelow_semibounded (V : ℝ → ℝ)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) {c : ℝ} (hVc : ∀ x, -c ≤ V x) :
    SemiboundedBelowOn (ccDomain ℝ) (wallHam V hV) c := by sorry
