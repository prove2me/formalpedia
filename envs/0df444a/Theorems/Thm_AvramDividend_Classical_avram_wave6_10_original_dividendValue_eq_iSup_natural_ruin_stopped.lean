-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_dividendValue_eq_iSup_natural_ruin_stopped
-- name    : AvramDividend.Classical.avram_wave6_10_original_dividendValue_eq_iSup_natural_ruin_stopped
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:04:02.447274+00:00
-- url     : https://prove2.me/theorems/5cd004b0-5211-40a3-9bea-c57d768c4832
-- title:
--   Full original dividendValue equals the supremum of natural ruin-stopped discounted Stieltjes payments
-- statement:
--   For any original SpectrallyNegativeLevy and actual admissible original dividend regulator, the complete expected discounted Stieltjes dividendValue equals the supremum over natural n of the exact same expected payment integral on paymentTimes(min(ruinTime,n)). The earlier Proved value-iSup theorem uses closed horizons Iic n, while the stopped clock uses the strict interval Iio n; compare by choosing n+1 for each closed horizon, with the same original probability and payment measure. All initial and terminal atoms are preserved as n grows. Neither positive discount nor a bounded-variation or Gaussian assumption is required.
-- source:
--   Proved full-value integer closed-horizon supremum 3b737955-7611-4616-acb5-10f4f8025612, positive-clock exact paymentTimes intersection 3634eef8-1dc4-4ba5-9478-4dbce286da9e, and stopped-clock subset 153734f3 (previously accepted). Exact ENNReal outer and inner lintegral_mono and order-theoretic iSup bounds. A stronger reusable exact local-to-global identity for UBV 61bbf167 to 132447c8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_ofReal_eq_inter_Iio_of_pos
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_ofReal_subset_inter_horizon

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_10_original_dividendValue_eq_iSup_natural_ruin_stopped
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D) :
    dividendValue X q x D =
      ⨆ n : ℕ,
        ∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P := by sorry
