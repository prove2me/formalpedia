-- Prove2me | Theorems.Thm_BookProof_ScalaronWallEsa_wallHam_weak_eq
-- name    : BookProof.ScalaronWallEsa.wallHam_weak_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:41:08.2137+00:00
-- url     : https://prove2.me/theorems/13effa58-d2c7-4fcc-81b2-9f53aaffd05d
-- title:
--   The Lean 4 theorem `wallHam_weak_eq` in the `ChapterScalaronWallEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `wallHam_weak_eq` in the `ChapterScalaronWallEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronWallEsa.lean

-- Generated from ChapterScalaronWallEsa.lean — theorem BookProof.ScalaronWallEsa.wallHam_weak_eq
import Mathlib
import Definitions.Def_ChapterScalaronWallEsa
open BookProof.ScalaronWallEsa












open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.Starobinsky BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent
open BookProof.WeakSecondDeriv

noncomputable section

theorem BookProof.ScalaronWallEsa.wallHam_weak_eq (V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (z : ℂ)
    (u : Lp ℂ 2 (volume : Measure ℝ))
    (hu : ∀ v : ccDomain ℝ,
      (inner ℂ (wallHam V hV v) u : ℂ) = z * inner ℂ (v : Lp ℂ 2 _) u)
    {g : ℝ → ℝ} (hg : IsTestFun g) :
    ∫ x, ((deriv (deriv g) x : ℝ) : ℂ) * u x
      = ∫ x, ((g x : ℝ) : ℂ) * ((((V x : ℝ) : ℂ) - z) * u x) := by sorry
