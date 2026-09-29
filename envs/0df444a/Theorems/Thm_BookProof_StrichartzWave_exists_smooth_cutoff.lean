-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_exists_smooth_cutoff
-- name    : BookProof.StrichartzWave.exists_smooth_cutoff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:38:46.410872+00:00
-- url     : https://prove2.me/theorems/56b3b4dc-7612-443a-a08c-25dca38000e1
-- title:
--   The Lean 4 theorem `exists_smooth_cutoff` in the `ChapterStrichartzWave` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `exists_smooth_cutoff` in the `ChapterStrichartzWave` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStrichartzWave.lean

-- Generated from ChapterStrichartzWave.lean — theorem BookProof.StrichartzWave.exists_smooth_cutoff
import Mathlib
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave










open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

omit [MeasurableSpace V] [BorelSpace V] in

theorem BookProof.StrichartzWave.exists_smooth_cutoff (R : ℝ) :
    ∃ χ : V → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧
      (∀ x, ‖x‖ ≤ R → χ x = 1) ∧ (∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x, R + 1 ≤ ‖x‖ → χ x = 0) ∧ ∃ C : ℝ, ∀ x, ‖gradient χ x‖ ≤ C := by sorry
