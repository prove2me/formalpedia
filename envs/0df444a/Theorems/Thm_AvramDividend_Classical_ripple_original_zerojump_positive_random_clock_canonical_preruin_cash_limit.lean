-- Prove2me | Theorems.Thm_AvramDividend_Classical_ripple_original_zerojump_positive_random_clock_canonical_preruin_cash_limit
-- name    : AvramDividend.Classical.ripple_original_zerojump_positive_random_clock_canonical_preruin_cash_limit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T17:14:19.007166+00:00
-- url     : https://prove2.me/theorems/47b06535-ff76-44b7-96db-25b37ea29f0a
-- title:
--   Original positive random stopping clock: canonical strictly preclock discounted Stieltjes cash converges to actual prepayment terminal including ruin contact
-- statement:
--   For the original zero-jump spectrally negative Levy controlled dividend process, an arbitrary actual positive random stopping clock no later than ruin has a canonical original physical strict-preclock sequence obtained by subtracting the clock divided by the growing positive integer mesh count. Prove that along almost every sample path, without any additional selected sequence, the discounted true post-right-payment reserve value and strict Stieltjes dividend cash at these strictly earlier physical times converge to the original true PREpayment terminal value plus the dividend cash excluding the stopping-time atom. This is source-faithful at rho=ruin and handles the exact terminal state needed for the full original finite-cap Ito–Stieltjes residual.
-- source:
--   Existing proved avram_gclose17_original_cofinal_strict_reward_left_limit 2151ad9a-4187-47c8-83d2-9b08fb95f231 and proved positive clock cofinal sequence geometry 58277187-7bac-42dd-97f5-92f4347c95eb; source 0ef5d778-7536-4a04-90bc-68e0b5c21262.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gclose17_original_cofinal_strict_reward_left_limit
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_contact_left_endpoint_approach_certificate
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem AvramDividend.Classical.ripple_original_zerojump_positive_random_clock_canonical_preruin_cash_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (q : ℝ) (hq : 0 < q)
    (ρ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P,
      0 < ρ ω → (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω →
      Tendsto
        (fun j =>
          let s : ℝ≥0 := ρ ω - ρ ω / ((j : ℝ≥0) + 1)
          Real.exp (-(q * (s : ℝ))) *
            w (x + X.X s ω - rightLimit D s ω) +
          (∫⁻ z in paymentTimes (ruinTime X x D ω) ∩ Iio (s : ℝ),
            ENNReal.ofReal (Real.exp (-(q * z)))
            ∂(dividendMeasure D ω)).toReal)
        atTop
        (𝓝 (Real.exp (-(q * (ρ ω : ℝ))) *
            w (riskProcess X x D (ρ ω) ω) +
          (∫⁻ z in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * z)))
            ∂(dividendMeasure D ω)).toReal)) := by sorry
