-- Prove2me | solution 1 for result_001_avram_dividend_classical_avram_chat24_bv_compact_integrability_09b2e7a8
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T07:56:18.507309+00:00
-- url     : https://prove2.me/submissions/d5658e95-1b9b-426b-b06f-7647a936398a

import Mathlib.Probability.Process.Filtration
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical

noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (w : ℝ → ℝ) (hwm : Measurable w)
    (q a b L R A : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hW : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (hDeriv : ∀ y ∈ Icc a b, |deriv w y| ≤ A)
    (hGen : ∀ y ∈ Icc a b, X.GeneratorIntegrable w y)
    {ι : Type*} [MeasurableSpace ι] (μ : Measure ι) [IsFiniteMeasure μ]
    (Y e : ι → ℝ) (hYm : Measurable Y) (hem : Measurable e)
    (he : ∀ t, |e t| ≤ 1) (E : Set ι) (hEm : MeasurableSet E)
    (hE : ∀ t ∈ E, Y t ∈ Icc a b) 
    (hJm : (let J : ℝ → ℝ := fun y => ∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν; let F : ι → ℝ := (fun t => if t ∈ E then e t * (X.drift * deriv w (Y t) - q * w (Y t)) else 0); let G : ι → ℝ := (fun t => if t ∈ E then e t * (X.drift * deriv w (Y t) + J (Y t) - q * w (Y t)) else 0); Measurable J))
    (hFm : (let J : ℝ → ℝ := fun y => ∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν; let F : ι → ℝ := (fun t => if t ∈ E then e t * (X.drift * deriv w (Y t) - q * w (Y t)) else 0); let G : ι → ℝ := (fun t => if t ∈ E then e t * (X.drift * deriv w (Y t) + J (Y t) - q * w (Y t)) else 0); Measurable F))
    (hGm : (let J : ℝ → ℝ := fun y => ∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν; let F : ι → ℝ := (fun t => if t ∈ E then e t * (X.drift * deriv w (Y t) - q * w (Y t)) else 0); let G : ι → ℝ := (fun t => if t ∈ E then e t * (X.drift * deriv w (Y t) + J (Y t) - q * w (Y t)) else 0); Measurable G))
    : (let J : ℝ → ℝ := fun y => ∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν; let F : ι → ℝ := (fun t => if t ∈ E then e t * (X.drift * deriv w (Y t) - q * w (Y t)) else 0); let G : ι → ℝ := (fun t => if t ∈ E then e t * (X.drift * deriv w (Y t) + J (Y t) - q * w (Y t)) else 0); Integrable F μ) := by
  change Measurable (fun t => if t ∈ E then
    e t * (X.drift * deriv w (Y t) - q * w (Y t)) else 0) at hFm
  change Integrable (fun t => if t ∈ E then
    e t * (X.drift * deriv w (Y t) - q * w (Y t)) else 0) μ
  let M : ℝ := |X.drift| * A + |q| * R
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hraw : ∀ y ∈ Icc a b, |X.drift * deriv w y - q * w y| ≤ M := by
    intro y hy
    have hwy := hW y hy.2
    calc
      |X.drift * deriv w y - q * w y| ≤
          |X.drift * deriv w y| + |q * w y| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              (abs_sub_le (X.drift * deriv w y) (0 : ℝ) (q * w y))
      _ = |X.drift| * |deriv w y| + |q| * |w y| := by rw [abs_mul, abs_mul]
      _ ≤ M := add_le_add
        (mul_le_mul_of_nonneg_left (hDeriv y hy) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hwy (abs_nonneg _))
  have hbound : ∀ t, ‖(if t ∈ E then
      e t * (X.drift * deriv w (Y t) - q * w (Y t)) else 0)‖ ≤ M := by
    intro t
    by_cases ht : t ∈ E
    · simp only [if_pos ht, Real.norm_eq_abs, abs_mul]
      calc
        |e t| * |X.drift * deriv w (Y t) - q * w (Y t)| ≤
          1 * |X.drift * deriv w (Y t) - q * w (Y t)| :=
            mul_le_mul_of_nonneg_right (he t) (abs_nonneg _)
        _ = |X.drift * deriv w (Y t) - q * w (Y t)| := one_mul _
        _ ≤ M := hraw (Y t) (hE t ht)
    · simp only [if_neg ht, norm_zero]
      exact hM
  exact Integrable.of_bound hFm.aestronglyMeasurable M
    (Filter.Eventually.of_forall hbound)
end

