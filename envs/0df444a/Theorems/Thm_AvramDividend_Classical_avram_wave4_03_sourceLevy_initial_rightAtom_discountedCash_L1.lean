-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_initial_rightAtom_discountedCash_L1
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_initial_rightAtom_discountedCash_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:08:05.863607+00:00
-- url     : https://prove2.me/theorems/faf268c0-ffb2-4027-8045-5d649cf032c3
-- title:
--   Original same-source initial right dividend atom exponential payout is L1 and bounded by one
-- statement:
--   For the actual original source filtered Lévy process X and its adapted left-continuous strategy D, the exact initial right-payment atom weighted by θ exp(-θ D0+) is a nonnegative integrable random variable bounded by 1. The result is an authentic initial Stieltjes mass needed in the true closed-horizon expected stochastic bound.
-- source:
--   Original source dividend rightLimit adaptedness, nonnegative D and scalar exponential control loss; same finite measure P supplied by X.isProbability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_exponential_control_loss_dominates_discounted_dividend_increment
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_initial_rightAtom_discountedCash_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => θ * Real.exp (-(θ * rightLimit D 0 ω)) *
      rightLimit D 0 ω) P ∧
    ∀ ω, 0 ≤ θ * Real.exp (-(θ * rightLimit D 0 ω)) *
      rightLimit D 0 ω ∧
      θ * Real.exp (-(θ * rightLimit D 0 ω)) *
        rightLimit D 0 ω ≤ 1 := by sorry
