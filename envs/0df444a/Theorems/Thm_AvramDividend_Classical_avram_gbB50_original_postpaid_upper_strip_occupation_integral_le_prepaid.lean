-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB50_original_postpaid_upper_strip_occupation_integral_le_prepaid
-- name    : AvramDividend.Classical.avram_gbB50_original_postpaid_upper_strip_occupation_integral_le_prepaid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:16:31.263183+00:00
-- url     : https://prove2.me/theorems/789c3f87-9988-4110-8760-5f2c8093aa71
-- title:
--   Original physical-time postpayment upper-strip occupation is bounded by the true prepayment occupation charge
-- statement:
--   For any original controlled dividend path and bounded positive time window, the time spent with the postpayment reserve above a finite clipping level is at most the time spent with the prepayment riskProcess above that level. Integrability of the two original indicator functions is explicit. This converts the source-faithful caplinear HJB time drift into the exact prepayment occupation charge appearing in Gaussian B21.
-- source:
--   Pointwise pre/post reserve indicator domination B49, integrability hypotheses for the two original physical-time indicators, and integral_mono_ae on the exact stopped volume window.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB49_original_postpaid_upper_strip_indicator_le_true_prepaid
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB50_original_postpaid_upper_strip_occupation_integral_le_prepaid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω)
    (hIpost : IntegrableOn
      (fun t : ℝ =>
        if t < (ρ ω : ℝ) ∧
            b < x + X.X (Real.toNNReal t) ω -
              rightLimit D (Real.toNNReal t) ω
        then (1 : ℝ) else 0)
      (Ioo (0 : ℝ) (n : ℝ)) volume)
    (hIpre : IntegrableOn
      (fun t : ℝ =>
        if t < (ρ ω : ℝ) ∧
            b < riskProcess X x D (Real.toNNReal t) ω
        then (1 : ℝ) else 0)
      (Ioo (0 : ℝ) (n : ℝ)) volume) :
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (ρ ω : ℝ) ∧
          b < x + X.X (Real.toNNReal t) ω -
            rightLimit D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume) ≤
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (ρ ω : ℝ) ∧
          b < riskProcess X x D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume) := by sorry
