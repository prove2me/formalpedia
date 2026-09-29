-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_inner_toLp_eq_integral_fourier
-- name    : BookProof.StrichartzWave.inner_toLp_eq_integral_fourier
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:41:35.300666+00:00
-- url     : https://prove2.me/theorems/f98ec1b4-8b36-47d0-9f99-001b8779f814
-- title:
--   The Lean 4 theorem `inner_toLp_eq_integral_fourier` in the `ChapterStrichartzWave` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `inner_toLp_eq_integral_fourier` in the `ChapterStrichartzWave` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStrichartzWave.lean

-- Generated from ChapterStrichartzWave.lean — theorem BookProof.StrichartzWave.inner_toLp_eq_integral_fourier
import Mathlib
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave










open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

theorem BookProof.StrichartzWave.inner_toLp_eq_integral_fourier (f g : 𝓢(V, ℂ)) :
    (inner ℂ (f.toLp 2 (volume : Measure V)) (g.toLp 2 (volume : Measure V)) : ℂ)
      = ∫ x, (starRingEnd ℂ) ((𝓕 f : 𝓢(V, ℂ)) x) * ((𝓕 g : 𝓢(V, ℂ)) x) := by sorry
