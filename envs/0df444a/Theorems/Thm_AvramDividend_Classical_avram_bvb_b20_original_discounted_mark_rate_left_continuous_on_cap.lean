-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_original_discounted_mark_rate_left_continuous_on_cap
-- name    : AvramDividend.Classical.avram_bvb_b20_original_discounted_mark_rate_left_continuous_on_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:42:49.83178+00:00
-- url     : https://prove2.me/theorems/70cfb20d-8407-4b37-8272-aa47a38bde8a
-- title:
--   Original discounted diffuse-mark compensator kernel is left-continuous at cap contact
-- statement:
--   The original discounted finite-activity mark-integrated reserve kernel is left-continuous at each positive closed-cap contact on a drift-only original path, preserving the original probability space and admissible dividends.
-- source:
--   Original no-jump weighted compensator continuity for the one-sided mesh inequality of phys95 and later-ruin quadrature.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_original_mark_rate_left_continuous_on_cap
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b20_original_discounted_mark_rate_left_continuous_on_cap
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
    (hνatom : ∀ a : ℝ, X.ν {a} = 0) (q : ℝ) :
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) r
    let A : Set ℝ := {b | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}
    (0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C) →
    ContinuousWithinAt
      (fun r : ℝ≥0 => Real.exp (-(q * (r : ℝ))) *
        ∫ z in Iio (0 : ℝ), w (U r + z) - w (U r) ∂X.ν)
      (Ioc 0 t ∩ U ⁻¹' A) t := by sorry
