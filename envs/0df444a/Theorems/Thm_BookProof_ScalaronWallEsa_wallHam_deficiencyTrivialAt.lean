-- Prove2me | Theorems.Thm_BookProof_ScalaronWallEsa_wallHam_deficiencyTrivialAt
-- name    : BookProof.ScalaronWallEsa.wallHam_deficiencyTrivialAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:42:16.54638+00:00
-- url     : https://prove2.me/theorems/0e419eff-9513-4a15-8f36-49ee0a9f47e2
-- title:
--   The Lean 4 theorem `wallHam_deficiencyTrivialAt` in the `ChapterScalaronWallEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `wallHam_deficiencyTrivialAt` in the `ChapterScalaronWallEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronWallEsa.lean

-- Generated from ChapterScalaronWallEsa.lean — theorem BookProof.ScalaronWallEsa.wallHam_deficiencyTrivialAt
import Mathlib
import Definitions.Def_ChapterScalaronWallEsa
open BookProof.ScalaronWallEsa












open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.Starobinsky BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent
open BookProof.WeakSecondDeriv

noncomputable section

theorem BookProof.ScalaronWallEsa.wallHam_deficiencyTrivialAt (V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVnn : ∀ x, 0 ≤ V x) {z : ℂ} (hz : z.re = 0) :
    DeficiencyTrivialAt (ccDomain ℝ) (wallHam V hV) z := by sorry
