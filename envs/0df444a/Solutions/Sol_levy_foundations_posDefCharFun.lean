-- Prove2me | solution 1 for levy_foundations_posDefCharFun
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-03T23:22:46.107318+00:00
-- url     : https://prove2.me/submissions/bc032f45-ad8b-4a1c-817f-5529624e3a2f

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_levy_foundations_isPositiveDefinite

open MeasureTheory

theorem levy_sum_eq (μ : Measure ℝ) [IsFiniteMeasure μ] {n : ℕ} (ξ : Fin n → ℝ) (c : Fin n → ℂ) :
    ∑ j, ∑ k, starRingEnd ℂ (c j) * c k * charFun μ (ξ j - ξ k) =
      ((∫ t, ‖∑ k, c k * Complex.exp (((-(ξ k * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  have hint : ∀ j k, Integrable (fun t : ℝ => starRingEnd ℂ (c j) * c k *
      Complex.exp ((((ξ j - ξ k) * t : ℝ) : ℂ) * Complex.I)) μ := by
    intro j k
    refine Integrable.const_mul ?_ _
    refine Integrable.of_bound (C := 1) ?_ ?_
    · exact (by fun_prop : Continuous fun t : ℝ =>
        Complex.exp ((((ξ j - ξ k) * t : ℝ) : ℂ) * Complex.I)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t => by rw [Complex.norm_exp_ofReal_mul_I]
  have h1 : ∀ j k, starRingEnd ℂ (c j) * c k * charFun μ (ξ j - ξ k) =
      ∫ t, starRingEnd ℂ (c j) * c k *
        Complex.exp ((((ξ j - ξ k) * t : ℝ) : ℂ) * Complex.I) ∂μ := by
    intro j k
    rw [charFun_apply_real, integral_const_mul]
    simp only [Complex.ofReal_mul]
  simp_rw [h1]
  have h2 : ∀ j, ∑ k, ∫ t, starRingEnd ℂ (c j) * c k *
        Complex.exp ((((ξ j - ξ k) * t : ℝ) : ℂ) * Complex.I) ∂μ =
      ∫ t, ∑ k, starRingEnd ℂ (c j) * c k *
        Complex.exp ((((ξ j - ξ k) * t : ℝ) : ℂ) * Complex.I) ∂μ := fun j =>
    (integral_finsetSum _ fun k _ => hint j k).symm
  simp_rw [h2]
  rw [← integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k,
    ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [Complex.ofReal_pow, ← Complex.conj_mul', map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, ← Complex.exp_conj]
  have : starRingEnd ℂ (((-(ξ j * t) : ℝ) : ℂ) * Complex.I) + (((-(ξ k * t) : ℝ) : ℂ) * Complex.I)
      = (((ξ j - ξ k) * t : ℝ) : ℂ) * Complex.I := by
    simp
    ring
  rw [← this, Complex.exp_add]
  ring

theorem solution (μ : ProbabilityMeasure ℝ) :
    LevyFoundations.isPositiveDefinite
      (fun ξ : ℝ => charFun (μ : Measure ℝ) ξ) := by
  intro n x c
  simp only
  rw [levy_sum_eq]
  open scoped ComplexOrder in
  exact Complex.zero_le_real.mpr (integral_nonneg fun t => by positivity)
