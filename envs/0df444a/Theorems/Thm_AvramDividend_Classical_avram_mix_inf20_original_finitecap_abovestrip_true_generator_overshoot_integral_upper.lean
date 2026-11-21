-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_abovestrip_true_generator_overshoot_integral_upper
-- name    : AvramDividend.Classical.avram_mix_inf20_original_finitecap_abovestrip_true_generator_overshoot_integral_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:41:23.1169+00:00
-- url     : https://prove2.me/theorems/9b5f4ed4-7994-41f7-8cd2-67a15b1990b1
-- title:
--   Original mixed Levy finitecap above-barrier generator upper bound by drift plus genuine negative jump ruin-overshoot integral
-- statement:
--   Genuine original spectrally negative Lévy generator (with exact triplet Gaussian σ, drift c, and small-negative-jump truncation) for a finite-cap candidate V that extends w linearly above C. Under the explicitly required original GeneratorIntegrable and integrable positive ruin overshoot moment, its full generator at y>C is bounded by triplet drift plus the actual ν-expectation of ruin overshoot max(0,-(y+z)). This is a nontrivial source-true integrated consequence of Proved above-strip Gaussian curvature zero and exact generator identity, plus the original generatorIntegrand pointwise negative-mark overshoot bound; use Mathlib ae_restrict_mem and integral_mono_ae to compare actual ν.restrict(Iio 0) Bochner integrals. It converts deterministic jump estimates to a ready-to-insert HJB drift estimate for the original stopped mixed infinite-activity Itô-Meyer proof. No integrability is inferred without a hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_finitecap_abovestrip_true_generator_overshoot_integral_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (V : ℝ → ℝ)
    (hV : ∀ t : ℝ, V t =
      if t ≤ C.toReal then w t
      else w C.toReal + (t - C.toReal))
    (y : ℝ) (hy : C.toReal < y)
    (hGen : X.GeneratorIntegrable V y)
    (hOver : Integrable (fun z : ℝ => max 0 (-(y + z)))
      (X.ν.restrict (Iio (0 : ℝ)))) :
    X.generator V y ≤ X.c +
      (∫ z in Iio (0 : ℝ), max 0 (-(y + z)) ∂X.ν) := by sorry
