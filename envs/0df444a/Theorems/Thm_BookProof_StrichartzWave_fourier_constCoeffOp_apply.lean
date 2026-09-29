-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_fourier_constCoeffOp_apply
-- name    : BookProof.StrichartzWave.fourier_constCoeffOp_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:41:12.922964+00:00
-- url     : https://prove2.me/theorems/a8d869b0-14e4-487c-b3d2-9cd7bcc6c0bb
-- title:
--   The Lean 4 theorem `fourier_constCoeffOp_apply` in the `ChapterStrichartzWave` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `fourier_constCoeffOp_apply` in the `ChapterStrichartzWave` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStrichartzWave.lean

-- Generated from ChapterStrichartzWave.lean — theorem BookProof.StrichartzWave.fourier_constCoeffOp_apply
import Mathlib
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave










open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

theorem BookProof.StrichartzWave.fourier_constCoeffOp_apply (c : ι → ℝ) (w : ι → V) (κ : ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    (𝓕 (constCoeffOp c w κ f) : 𝓢(V, ℂ)) x
      = ((symbolFn c w κ x : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x := by sorry
