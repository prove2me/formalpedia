-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_integral_conj_mul_symbol_sub_eq_zero
-- name    : BookProof.StrichartzWave.integral_conj_mul_symbol_sub_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:42:43.360989+00:00
-- url     : https://prove2.me/theorems/42676c87-f82b-4fd1-b289-9b1fca4d6575
-- title:
--   The Lean 4 theorem `integral_conj_mul_symbol_sub_eq_zero` in the `ChapterStrichartzWave` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `integral_conj_mul_symbol_sub_eq_zero` in the `ChapterStrichartzWave` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStrichartzWave.lean

-- Generated from ChapterStrichartzWave.lean — theorem BookProof.StrichartzWave.integral_conj_mul_symbol_sub_eq_zero
import Mathlib
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave










open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

theorem BookProof.StrichartzWave.integral_conj_mul_symbol_sub_eq_zero (c : ι → ℝ) (w : ι → V) (κ : ℝ) (z : ℂ)
    (u : Lp ℂ 2 (volume : Measure V))
    (hu : ∀ v : schwartzDomain V,
      (inner ℂ (opL2 (constCoeffOp c w κ) v) u : ℂ) = z * inner ℂ (v : Lp ℂ 2 _) u)
    (ψ : 𝓢(V, ℂ)) :
    ∫ x, (starRingEnd ℂ) (ψ x) * (((symbolFn c w κ x : ℝ) : ℂ) - z) *
      ((𝓕 u : Lp ℂ 2 (volume : Measure V)) x) = 0 := by sorry
