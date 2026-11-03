-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_strict_preruin_random_clock_real_mean_to_ennreal
-- name    : AvramDividend.Classical.avram_wave7_03_original_strict_preruin_random_clock_real_mean_to_ennreal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:12:15.341315+00:00
-- url     : https://prove2.me/theorems/59216c01-c2ea-4ec6-9c02-8a18c7c383b1
-- title:
--   Original strict pre-ruin random-clock signed-real Stieltjes expectation equals the full ENNReal payout
-- statement:
--   For the true original Lévy process X, genuine dividend measure and same ruin time on P, take a random finite clock τ which is zero or strictly before ruin P-almost surely. If the actual real discounted Stieltjes cash on the chronological closed interval [0,τ] is L1-integrable under P, its original real expectation embeds exactly as the double ENNReal lintegral over paymentTimes(ruinTime) ∩ Iic τ. The real integrand exp(-qt) is nonnegative and the accepted pathwise same-measure bridge gives equality of cash on the conull pre-ruin set. No earlier ENNReal expected budget, no change of stochastic model, and no atomic-only assumption is required; time zero and singular-continuous payments are preserved.
-- source:
--   Proved strict pre-ruin closed real/ENNReal equality W7-03 2b209825 (when accepted); Mathlib ofReal_integral_eq_lintegral_ofReal with explicit nonnegativity and supplied real L1 integrability; original dividend definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_strict_preruin_closed_real_ennreal_eq

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_strict_preruin_random_clock_real_mean_to_ennreal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (τ : Ω → ℝ≥0)
    (hPre : ∀ᵐ ω ∂P,
      τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω)
    (hRealInt : Integrable (fun ω =>
      ∫ t in Icc (0 : ℝ) (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    ENNReal.ofReal
      (∫ ω, (∫ t in Icc (0 : ℝ) (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
