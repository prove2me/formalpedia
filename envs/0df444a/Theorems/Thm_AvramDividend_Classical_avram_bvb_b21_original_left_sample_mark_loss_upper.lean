-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_left_sample_mark_loss_upper
-- name    : AvramDividend.Classical.avram_bvb_b21_original_left_sample_mark_loss_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:02:59.064073+00:00
-- url     : https://prove2.me/theorems/364b1bea-d330-4a11-9459-234df2d15b85
-- title:
--   Unconditional original left-sampled marked-loss upper bound at contact
-- statement:
--   On a no-jump original physical path, any positive left-approaching reserve sampling sequence has its masked open-interior negative mark loss eventually bounded by the true closed-cap mark loss at the contact time, including excursions outside the cap.
-- source:
--   Root-connected contact-safe a.e. pointwise limsup substep for original BV phys95 and later-ruin quadrature.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_original_open_mark_loss_upper_at_contact
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_closed_cap_negative_mark_rate_nonpos
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b21_original_left_sample_mark_loss_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S) (htpos : 0 < t)
    (hsource : ∀ r : ℝ≥0, r ≤ S → X.X r ω = (r : ℝ) * X.drift)
    (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0) (hw_meas : Measurable w)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (hνatom : ∀ a : ℝ, X.ν {a} = 0) (q : ℝ)
    (s : ℕ → ℝ≥0) (hs : Tendsto s atTop (𝓝 t))
    (hleft : ∀ᶠ n in atTop, 0 < s n ∧ s n ≤ t)
    (ε : ℝ) (hε : 0 < ε) :
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
    (0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C) →
    ∀ᶠ n in atTop,
      (if 0 < U (s n) ∧ ENNReal.ofReal (U (s n)) < C then
        -(Real.exp (-(q * (s n : ℝ))) *
          ∫ z in Iio (0 : ℝ), w (U (s n) + z) - w (U (s n)) ∂X.ν)
       else 0) ≤
      -(Real.exp (-(q * (t : ℝ))) *
        ∫ z in Iio (0 : ℝ), w (U t + z) - w (U t) ∂X.ν) + ε := by sorry
