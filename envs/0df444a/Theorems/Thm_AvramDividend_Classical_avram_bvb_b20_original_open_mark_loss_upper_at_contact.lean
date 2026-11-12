-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_original_open_mark_loss_upper_at_contact
-- name    : AvramDividend.Classical.avram_bvb_b20_original_open_mark_loss_upper_at_contact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:21:37.485457+00:00
-- url     : https://prove2.me/theorems/1d1a2802-30d3-47e3-b345-37c0abbf0249
-- title:
--   Source-exact original positive-time open-grid mark loss has closed-cap upper envelope
-- statement:
--   On the exact original spectrally negative Levy and admissible right-payment reserve path, the discounted open-grid negative-mark loss is eventually bounded by the closed-cap contact-time loss plus an arbitrary error. The BV full-cap gradient assumptions discharge the negative-mark sign without additional hypotheses.
-- source:
--   Root-connected local one-sided quadrature ingredient for phys95, 53b0 and original source 4f605d76.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_original_open_mask_local_upper_closed_mark_loss
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_closed_cap_negative_mark_rate_nonpos
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b20_original_open_mark_loss_upper_at_contact
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
    (ε : ℝ) (hε : 0 < ε) :
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) r
    let A : Set ℝ := {b | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}
    (0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C) →
    ∀ᶠ r in 𝓝[Ioc 0 t ∩ U ⁻¹' A] t,
      (if 0 < U r ∧ ENNReal.ofReal (U r) < C then
        -(Real.exp (-(q * (r : ℝ))) *
          ∫ z in Iio (0 : ℝ), w (U r + z) - w (U r) ∂X.ν)
       else 0) ≤
      -(Real.exp (-(q * (t : ℝ))) *
        ∫ z in Iio (0 : ℝ), w (U t + z) - w (U t) ∂X.ν) + ε := by sorry
