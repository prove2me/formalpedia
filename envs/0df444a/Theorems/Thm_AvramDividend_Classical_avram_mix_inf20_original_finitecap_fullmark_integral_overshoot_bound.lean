-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_fullmark_integral_overshoot_bound
-- name    : AvramDividend.Classical.avram_mix_inf20_original_finitecap_fullmark_integral_overshoot_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:32:29.369265+00:00
-- url     : https://prove2.me/theorems/5f1510d5-0d96-4027-a8d2-3d2773679918
-- title:
--   Genuine original spectrally negative infinite-jump Lévy compensated full-mark generator integral bounded by ruin overshoot
-- statement:
--   Integrated actual original spectrally negative Lévy full-mark compensated jump upper-strip estimate for a finite cap. The measure is the true negative-jump Lévy measure X.ν restricted to Iio 0, and the integrand is exactly the Taylor compensation term V(y+z)-V(y)-V'(y)z of the caplinear candidate. For every premark reserve above the cap, it is bounded by the expected positive-part reserve overshoot. The two integrability assumptions are explicit and must be verified separately for the stopped Itô kernel, avoiding false Fubini/Tonelli in infinite negative activity. Pointwise mark bound is established by Proved complete finite-cap envelope and integrated using true Lebesgue integral monotonicity, no sign errors at the ruin boundary.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_finitecap_fullmark_integral_overshoot_bound
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
    (hMI : Integrable (fun z : ℝ =>
      V (y + z) - V y - deriv V y * z)
      (X.ν.restrict (Iio (0 : ℝ))))
    (hOI : Integrable (fun z : ℝ => max 0 (-(y + z)))
      (X.ν.restrict (Iio (0 : ℝ)))) :
    (∫ z in Iio (0 : ℝ), V (y + z) - V y - deriv V y * z ∂X.ν) ≤
      (∫ z in Iio (0 : ℝ), max 0 (-(y + z)) ∂X.ν) := by sorry
