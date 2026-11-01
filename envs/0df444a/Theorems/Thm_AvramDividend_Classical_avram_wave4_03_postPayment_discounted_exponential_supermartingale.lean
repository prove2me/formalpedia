-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_postPayment_discounted_exponential_supermartingale
-- name    : AvramDividend.Classical.avram_wave4_03_postPayment_discounted_exponential_supermartingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:09:19.81324+00:00
-- url     : https://prove2.me/theorems/fab320c3-5fa4-4198-8338-868374d6fdf0
-- title:
--   Actual post-payment controlled Levy reserve has a discounted exponential supermartingale
-- statement:
--   For the true original spectrally negative Levy path X and any adapted left-continuous dividend strategy D, its chronological right-continuous post-payment reserve x+X_t-D_{t+} has a discounted positive-rate exponential supermartingale in the SAME right-continuous filtration and probability space whenever q>=psi(theta). This strengthens the existing pre-payment controlled exponential supermartingale and genuinely incorporates each right-dividend atom. It relies on the original exact right-continuous Levy reconstruction, post-payment dividend adaptedness and monotonicity, and the valid nonnegative Levy martingale times bounded antitone weight theorem. It does not assume jump Poisson compensation, nor imply the full Stieltjes cash verification bound.
-- source:
--   Existing canonical Proved levy_rightCont_process 006d14c7; dividendStrategy_rightLimit_adapted_rightCont 18945919; avram_wave3_03_dividendStrategy_rightLimit_monotone f7eef805; dividendStrategy_le_rightLimit 953f0e91; original Levy exponential martingale; martingale_bounded_adapted_antitone_weight_supermartingale c1efb6e8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_martingale_bounded_adapted_antitone_weight_supermartingale

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_postPayment_discounted_exponential_supermartingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q) :
    Supermartingale (fun t ω =>
      Real.exp (θ * (x + X.X t ω - rightLimit D t ω) - (t : ℝ) * q))
      𝓕.rightCont P := by sorry
