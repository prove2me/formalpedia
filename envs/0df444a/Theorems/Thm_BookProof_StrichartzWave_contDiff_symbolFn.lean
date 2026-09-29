-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_contDiff_symbolFn
-- name    : BookProof.StrichartzWave.contDiff_symbolFn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:38:49.643041+00:00
-- url     : https://prove2.me/theorems/a6027fa0-a8ed-440e-8f09-bf48096ee240
-- title:
--   The Lean 4 theorem `contDiff_symbolFn` in the `ChapterStrichartzWave` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `contDiff_symbolFn` in the `ChapterStrichartzWave` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStrichartzWave.lean

-- Generated from ChapterStrichartzWave.lean — theorem BookProof.StrichartzWave.contDiff_symbolFn
import Mathlib
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave










open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in

theorem BookProof.StrichartzWave.contDiff_symbolFn (c : ι → ℝ) (w : ι → V) (κ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (symbolFn c w κ) := by sorry
