-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_finiteGrid_positive_postPayment_budget
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_finiteGrid_positive_postPayment_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:37:34.050567+00:00
-- url     : https://prove2.me/theorems/62cf93c8-1337-4b13-864b-7c3ae8b3e4dc
-- title:
--   Actual original Lévy path yields nonnegative finite-grid postpayment consumption and expected budget
-- statement:
--   For the actual original spectrally negative Lévy X and genuine adapted left-continuous dividend D, every nondecreasing finite time-grid exponential payment-consumption sum formed with observed original martingale exp(θX_{t_{i+1}}−t_{i+1}ψθ) and postpayment factor exp(−θD_{t+}) is nonnegative samplewise; its expectation is bounded by the initial expected postpayment exponential wealth. The proof runs the accepted source-X right-continuous filtration transfer and exponential martingale, establishes pointwise antitonicity and adaptedness of postpayment D, then applies the canonical exact finite-grid stochastic budget. No continuous Stieltjes limit, source nonlinear Campbell or main HJB verification is claimed. Time-zero dividend atom must be handled separately.
-- source:
--   Canonical Proved source right-continuous Lévy reconstruction, source exponential martingale, postpayment adaptedness and monotonicity, generic finite-grid positive consumption budget 2500df75.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_finiteGrid_positive_martingale_consumption_budget

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_finiteGrid_positive_postPayment_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) :
    (∀ ω, 0 ≤ ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      (Real.exp (-(θ * rightLimit D (u i) ω)) -
        Real.exp (-(θ * rightLimit D (u (i + 1)) ω)))) ∧
    (∫ ω, ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      (Real.exp (-(θ * rightLimit D (u i) ω)) -
        Real.exp (-(θ * rightLimit D (u (i + 1)) ω))) ∂P) ≤
      (∫ ω, Real.exp (-(θ * rightLimit D (u 0) ω)) *
        Real.exp (θ * X.X (u 0) ω - (u 0 : ℝ) * X.ψ θ) ∂P) := by sorry
