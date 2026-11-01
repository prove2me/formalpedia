-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_finiteGrid_postPayment_exponential_exact_balance
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_finiteGrid_postPayment_exponential_exact_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:28:20.717575+00:00
-- url     : https://prove2.me/theorems/c9cf3e93-b9da-4ca1-83ef-a4237cf24c16
-- title:
--   Actual source Lévy and true right-payment dividends satisfy finite-grid exponential cash balance
-- statement:
--   For the actual source spectrally negative Lévy process X on the original Ω, probability P, and adapted dividend strategy D, reconstruct its exact right-continuous filtration law without changing any sample path or characteristic. The nonnegative original compensated exponential martingale exp(θX_t−tψθ) and adapted right-dividend factor exp(−θD_{t+}) satisfy an exact expectation balance on every finite monotone partition. The left-hand sum measures post-observation exponential wealth consumed by the genuine right-payment dividend factor; no independent replacement process or fictitious PRM is assumed. This is an original-X finite-grid stochastic compensation identity including right-payment atoms, but does not prove convergence to full Stieltjes cash, generator control for general C1 test w, or the final BV verification theorem.
-- source:
--   Accepted exact same-path right-continuous Levy reconstruction 006d14c7, compensated exponential Levy martingale, rightLimit D adaptedness 18945919, rightLimit nonnegative bound 953f0e91, and exact finiteGrid martingale consumption balance 0d3263b6.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_martingale_finiteGrid_consumption_exact_expectation_balance

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_finiteGrid_postPayment_exponential_exact_balance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) :
    (∫ ω, ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      (Real.exp (-(θ * rightLimit D (u i) ω)) -
        Real.exp (-(θ * rightLimit D (u (i + 1)) ω))) ∂P) =
    (∫ ω, Real.exp (-(θ * rightLimit D (u 0) ω)) *
      Real.exp (θ * X.X (u 0) ω - (u 0 : ℝ) * X.ψ θ) ∂P) -
    (∫ ω, Real.exp (-(θ * rightLimit D (u n) ω)) *
      Real.exp (θ * X.X (u n) ω - (u n : ℝ) * X.ψ θ) ∂P) := by sorry
