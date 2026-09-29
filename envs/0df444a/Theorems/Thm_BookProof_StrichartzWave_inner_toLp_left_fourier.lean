-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_inner_toLp_left_fourier
-- name    : BookProof.StrichartzWave.inner_toLp_left_fourier
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:41:46.647103+00:00
-- url     : https://prove2.me/theorems/1d5ca30a-65e5-49d7-9cf7-888f6a42d499
-- title:
--   The Lean 4 theorem `inner_toLp_left_fourier` in the `ChapterStrichartzWave` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `inner_toLp_left_fourier` in the `ChapterStrichartzWave` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStrichartzWave.lean

-- Generated from ChapterStrichartzWave.lean — theorem BookProof.StrichartzWave.inner_toLp_left_fourier
import Mathlib
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave










open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

theorem BookProof.StrichartzWave.inner_toLp_left_fourier (f : 𝓢(V, ℂ)) (u : Lp ℂ 2 (volume : Measure V)) :
    (inner ℂ (f.toLp 2 (volume : Measure V)) u : ℂ)
      = ∫ x, (starRingEnd ℂ) ((𝓕 f : 𝓢(V, ℂ)) x) * ((𝓕 u : Lp ℂ 2 (volume : Measure V)) x) := by sorry
