-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_fourier_secondDeriv_apply
-- name    : BookProof.StrichartzWave.fourier_secondDeriv_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:39:05.622418+00:00
-- url     : https://prove2.me/theorems/79d98c14-6716-43cb-8ee1-6b1a4536cd42
-- title:
--   The Lean 4 theorem `fourier_secondDeriv_apply` in the `ChapterStrichartzWave` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `fourier_secondDeriv_apply` in the `ChapterStrichartzWave` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStrichartzWave.lean

-- Generated from ChapterStrichartzWave.lean — theorem BookProof.StrichartzWave.fourier_secondDeriv_apply
import Mathlib
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave










open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

theorem BookProof.StrichartzWave.fourier_secondDeriv_apply (f : 𝓢(V, ℂ)) (m : V) (x : V) :
    (𝓕 (secondDeriv m f) : 𝓢(V, ℂ)) x
      = ((-4 * Real.pi ^ 2 * (inner ℝ x m) ^ 2 : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x := by sorry
