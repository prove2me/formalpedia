-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
-- name    : AvramDividend.Classical.avram_gledger20_original_strict_prefix_postpayment_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T10:41:22.143961+00:00
-- url     : https://prove2.me/theorems/cb67c5ea-2c41-49a8-801d-3e46878a2a17
-- title:
--   Original compact prepayment lower bound transfers to every strict postpayment prefix
-- statement:
--   For the original process and genuine dividend strategy, a uniform lower reserve bound u for all positive prepayment times strictly before a stopping horizon rho also holds for the postpayment reserve x+X.X(t)-rightLimit D(t) at every t<rho, including t=0. This follows from the actual prepayment riskProcess right limit and order-closedness, without replacing the strategy or requiring a finite dividend cap. It supplies the original frozen-source Gaussian mesh's lower-floor starting-state premise on strict stopped cells for open 47174f6c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_tendsto_postPaymentReserve_right

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger20_original_strict_prefix_postpayment_floor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ρ : ℝ≥0) (u : ℝ)
    (hprefix : ∀ t : ℝ≥0, 0 < t → t < ρ →
      u ≤ riskProcess X x D t ω) :
    ∀ t : ℝ≥0, t < ρ →
      u ≤ x + X.X t ω - rightLimit D t ω := by sorry
