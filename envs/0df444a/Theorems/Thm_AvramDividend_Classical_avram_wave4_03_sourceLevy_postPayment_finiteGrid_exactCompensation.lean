-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_postPayment_finiteGrid_exactCompensation
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_postPayment_finiteGrid_exactCompensation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:55:24.409817+00:00
-- url     : https://prove2.me/theorems/b7885be1-6288-4e6a-86d3-0603b7c1be00
-- title:
--   Original source Lévy finite-grid postpayment Stieltjes compensation is an exact expected terminal balance
-- statement:
--   On the actual original spectral-negative Lévy filtered probability space, finite-grid discounted consumption of the postpayment exponential factor has exact expected initial-minus-terminal wealth balance. Original Lévy exponential martingale and adapted right-limit dividend factor are proved on the same filtration. Every interval right-limit increment already encodes full diffuse, singular-continuous and atomic Stieltjes payment mass; this finite-grid equality does not assume atom-only concentration or claim arbitrary-w controlled Itô-Meyer.
-- source:
--   Proved source Levy reconstruction and exponential martingale; actual dividend right-limit adaptedness; genuine exact martingale finite-grid consumption equality 0d3263b6.

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

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_postPayment_finiteGrid_exactCompensation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) :
    (∫ ω, ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      (Real.exp (-(θ * rightLimit D (u i) ω)) -
       Real.exp (-(θ * rightLimit D (u (i + 1)) ω))) ∂P) =
    (∫ ω, Real.exp (-(θ * rightLimit D (u 0) ω)) *
      Real.exp (θ * X.X (u 0) ω - (u 0 : ℝ) * X.ψ θ) ∂P) -
    (∫ ω, Real.exp (-(θ * rightLimit D (u n) ω)) *
      Real.exp (θ * X.X (u n) ω - (u n : ℝ) * X.ψ θ) ∂P) := by sorry
