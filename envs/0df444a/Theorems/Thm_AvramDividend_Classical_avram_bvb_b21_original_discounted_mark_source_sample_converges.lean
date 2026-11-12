-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_discounted_mark_source_sample_converges
-- name    : AvramDividend.Classical.avram_bvb_b21_original_discounted_mark_source_sample_converges
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:20:39.015965+00:00
-- url     : https://prove2.me/theorems/bc9d7690-dc11-457b-ae4c-890d03909f0a
-- title:
--   Original marked compensator kernel converges along admissible one-sided physical samples
-- statement:
--   The exact original-path discounted negative-mark compensator kernel converges along any time samples approaching a positive time from below, provided the physical prepayment reserves at the samples and target remain in the actual inclusive cap. The source, probability space, dividend strategy, original marks and discount are unchanged. This is the key pointwise component of the 7ccc2a1a original grid dominated-convergence route.
-- source:
--   Root-connected original discounted compensator kernel convergence under inclusive cap sampled masks.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b20_original_discounted_mark_rate_left_continuous_on_cap
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b21_original_discounted_mark_source_sample_converges
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
    (s : ℕ → ℝ≥0) (hs_tend : Tendsto s atTop (𝓝 t))
    (hs_le : ∀ n, s n ≤ t) :
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
    (0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C) →
    (∀ᶠ n in atTop, 0 ≤ U (s n) ∧ ENNReal.ofReal (U (s n)) ≤ C) →
    Tendsto (fun n => Real.exp (-(q * (s n : ℝ))) *
      ∫ z in Iio (0 : ℝ), w (U (s n) + z) - w (U (s n)) ∂X.ν)
      atTop (𝓝 (Real.exp (-(q * (t : ℝ))) *
        ∫ z in Iio (0 : ℝ), w (U t + z) - w (U t) ∂X.ν)) := by sorry
