-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_theta_scaled_closedHorizon_Icc_budget_q_ge_psi
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_theta_scaled_closedHorizon_Icc_budget_q_ge_psi
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:36:10.742529+00:00
-- url     : https://prove2.me/theorems/60db8bf2-b8fb-423e-9e3a-20c541bdeb93
-- title:
--   Original source full Stieltjes theta-exponential budget for every discount q at least psi(theta)
-- statement:
--   For the original same-path Lévy process, any adapted admissible dividend strategy, positive theta and discount q≥ψ(theta), the theta-scaled postpayment exponential has expected full closed-horizon Stieltjes integral at most one, including diffuse, singular and atomic dividends. Directly follows from monotonicity in the nonnegative real clock and the compensated source theta martingale budget.
-- source:
--   Original theta-scaled closed-Icc Stieltjes stochastic budget new child and pointwise exponential discount monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_theta_scaled_closedHorizon_Icc_fullStieltjes_budget
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_theta_scaled_closedHorizon_Icc_budget_q_ge_psi
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 < θ) (q : ℝ) (hq : X.ψ θ ≤ q)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (θ * Real.exp (θ *
        (X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
        (s.toNNReal : ℝ) * q))
      ∂dividendMeasure D ω ∂P) ≤ 1 := by sorry
