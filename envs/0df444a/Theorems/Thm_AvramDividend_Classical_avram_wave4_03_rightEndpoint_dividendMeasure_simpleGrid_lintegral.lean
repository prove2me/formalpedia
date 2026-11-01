-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_rightEndpoint_dividendMeasure_simpleGrid_lintegral
-- name    : AvramDividend.Classical.avram_wave4_03_rightEndpoint_dividendMeasure_simpleGrid_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:23:05.392394+00:00
-- url     : https://prove2.me/theorems/5d51d64e-b975-44a2-b403-36c27b629070
-- title:
--   Actual dividend measure: finite right-endpoint Stieltjes integrals equal postpayment increments, including diffuse mass
-- statement:
--   For any genuine adapted left-continuous dividend strategy, any sample path, arbitrary finite nonnegative right-endpoint step weights and times, the integral against the actual dividendMeasure is exactly a finite sum weighted by increments of rightLimit D. It uses the full Stieltjes measure: a purely atomic reduction is neither required nor valid. The theorem is pathwise, prior to stochastic expectations and right-endpoint convergence.
-- source:
--   Proved dividendMeasure_Ioc_rightLimit (UUID f9211de0) and pinned Mathlib lintegral_finset_sum, lintegral_indicator_const

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_rightEndpoint_dividendMeasure_simpleGrid_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ) (c : ℕ → ℝ≥0∞) :
    (∫⁻ t : ℝ, ∑ i ∈ Finset.range n,
      (Ioc (u i : ℝ) (u (i + 1) : ℝ)).indicator
        (fun _ : ℝ => c (i + 1)) t
      ∂dividendMeasure D ω) =
    ∑ i ∈ Finset.range n,
      c (i + 1) *
        ENNReal.ofReal
          (rightLimit D (u (i + 1)) ω -
            rightLimit D (u i) ω) := by sorry
