-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_uniform_pathwise_terminal_all_finite_clocks_ae_bound
-- name    : AvramDividend.Classical.avram_wave8_20_original_BV_uniform_pathwise_terminal_all_finite_clocks_ae_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:09:11.247773+00:00
-- url     : https://prove2.me/theorems/9b971456-ef21-4da3-b03e-df3d59d90473
-- title:
--   One common probability-one event bounds all source BV strict-survival terminal clocks up to H
-- statement:
--   For the original Standing BV Levy source and capped admissible dividend strategy, a single full-measure event and a single finite deterministic constant K dominate the positive-part discounted post-rightpayment terminal on strict survival simultaneously at every time t from zero through any fixed finite horizon H. This is a true uniform pathwise localisation envelope, robust to sample-dependent times, time grids and nonmonotone clock sequences. It uses only source physical drift and continuity of w, not the stopped martingale inequality.
-- source:
--   Original Avram Proposition 4(i), actual source BV deterministic physical drift ceiling 4a12fe1a and strict-survival postpayment solvency. This strengthens both ∀t≤H, ∀ᵐω terminal domination 370e0f69 and the W8-20 random-clock instantiation 2563fd4a by reversing the quantifiers to ∀ᵐω, ∀t≤H, enabling pathwise substitution of arbitrary random clocks without null-set exchange.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_postpayment_deterministic_horizon_upper_strip
import Theorems.Thm_AvramDividend_Classical_continuous_test_abs_le_on_finite_cap
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_nonnegative_strictly_before_ruin
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_BV_uniform_pathwise_terminal_all_finite_clocks_ae_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ H →
        (if (t : ℝ≥0∞) < ruinTime X x D ω then
          max 0 (Real.exp (-(q * (t : ℝ))) *
            w (x + X.X t ω - rightLimit D t ω))
        else 0) ≤ K := by sorry
