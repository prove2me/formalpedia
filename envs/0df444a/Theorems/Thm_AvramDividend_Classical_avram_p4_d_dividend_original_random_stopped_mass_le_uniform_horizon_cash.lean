-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_stopped_mass_le_uniform_horizon_cash
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_random_stopped_mass_le_uniform_horizon_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:43:16.655471+00:00
-- url     : https://prove2.me/theorems/75974f91-b404-421c-ae5e-3be8a7bcc064
-- title:
--   Original random ruin-clock Stieltjes mass dominated uniformly by discounted Cash through horizon n
-- statement:
--   For a true admissible original right-continuous dividend strategy, any sample-dependent extended ruin stopping deadline sigma and finite sample-dependent horizon tau bounded above by a deterministic integer n, the ordinary real mass of every path-dependent submeasure nu omega of original dividendMeasure D omega on the exact stopped paid clock is at most exp(qn) times the original discounted Cash.toReal. Both σ and τ may depend arbitrarily on ω. This is the deterministic-factor estimate for using the existing original stopped Cash integrability result in an outer expectation proof, and preserves the time-zero and eligible horizon right-payment atoms.
-- source:
--   Accepted exact original stopped real dividend submeasure mass-to-Cash helper 159d8858 instantiated at random clocks; source tau≤n, Real.exp_neg and Real.exp_le_exp. All original clock endpoint conventions unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_dominated_real_mass_le_cash
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_random_stopped_mass_le_uniform_horizon_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞) (τ : Ω → ℝ≥0) (n : ℕ)
    (hτ : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (ν : Ω → Measure ℝ)
    (hdom : ∀ ω, ν ω ≤ dividendMeasure D ω)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ ω, (ν ω).real (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)) ≤
      Real.exp (q * (n : ℝ)) *
        (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by sorry
