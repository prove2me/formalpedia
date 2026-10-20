-- Prove2me | Theorems.Thm_BookProof_StrichartzWave_integral_conj_mul_multiplier_sub_eq_zero
-- name    : BookProof.StrichartzWave.integral_conj_mul_multiplier_sub_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T23:19:28.295496+00:00
-- url     : https://prove2.me/theorems/f403481f-9881-46df-8639-3651f5798e32
-- title:
--   `BookProof.StrichartzWave.integral_conj_mul_multiplier_sub_eq_zero` (m : V → ℝ) (hm : Function.HasTemperateGrowth m) (z : ℂ) (u : Lp ℂ 2 (volume : Measure V)) (hu : ∀ v : schwartzD
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWaveUnboundedPotential`.
--
--   `BookProof.StrichartzWave.integral_conj_mul_multiplier_sub_eq_zero` (m : V → ℝ) (hm : Function.HasTemperateGrowth m) (z : ℂ) (u : Lp ℂ 2 (volume : Measure V)) (hu : ∀ v : schwartzDomain V, (inner ℂ (opL2 (multiplierOp m) v) u : ℂ) = z * inner ℂ (v : Lp ℂ 2 _) u) (ψ : 𝓢(V, ℂ)) : ∫ x, (starRingEnd ℂ) (ψ x) * (((m x : ℝ) : ℂ) - z) * ((𝓕 u : Lp ℂ 2 (volume : Measure V)) x) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.StrichartzWave.integral_conj_mul_multiplier_sub_eq_zero`.

-- Generated from ChapterWaveUnboundedPotential.lean — theorem BookProof.StrichartzWave.integral_conj_mul_multiplier_sub_eq_zero
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem BookProof.StrichartzWave.integral_conj_mul_multiplier_sub_eq_zero (m : V → ℝ) (hm : Function.HasTemperateGrowth m)
    (z : ℂ) (u : Lp ℂ 2 (volume : Measure V))
    (hu : ∀ v : schwartzDomain V,
      (inner ℂ (opL2 (multiplierOp m) v) u : ℂ) = z * inner ℂ (v : Lp ℂ 2 _) u)
    (ψ : 𝓢(V, ℂ)) :
    ∫ x, (starRingEnd ℂ) (ψ x) * (((m x : ℝ) : ℂ) - z) *
      ((𝓕 u : Lp ℂ 2 (volume : Measure V)) x) = 0 := by sorry
