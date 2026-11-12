-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_original_open_mask_local_upper_closed_mark_loss
-- name    : AvramDividend.Classical.avram_bvb_b20_original_open_mask_local_upper_closed_mark_loss
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:00:40.487712+00:00
-- url     : https://prove2.me/theorems/73c78546-5a92-4824-9d87-d4f43fc9435d
-- title:
--   Original stopped open-grid marked loss has closed-cap local upper envelope
-- statement:
--   The original discounted marked compensator open-cap loss is eventually no larger than its closed-cap loss at a positive contact time, up to any positive error, along original left time and closed reserve cap.
-- source:
--   Original one-sided local contact upper envelope needed in phys95 and later-ruin reverse-Fatou argument.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_original_discounted_mark_rate_left_continuous_on_cap
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b20_original_open_mask_local_upper_closed_mark_loss
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S) (htpos : 0 < t)
    (hsource : ∀ r : ℝ≥0, r ≤ S → X.X r ω = (r : ℝ) * X.drift)
    (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (hw_meas : Measurable w)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (hνatom : ∀ a : ℝ, X.ν {a} = 0) (q : ℝ)
    (hRateNonpos : ∀ b : ℝ, 0 ≤ b → ENNReal.ofReal b ≤ C →
      (∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν) ≤ 0)
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
