-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_surviving_random_clock_drift_envelope
-- name    : AvramDividend.Classical.avram_wave3_03_bv_surviving_random_clock_drift_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T23:27:55.539398+00:00
-- url     : https://prove2.me/theorems/dea62233-e54c-4030-9aeb-f86faf6c6241
-- title:
--   Random-clock BV surviving Stieltjes payout bounded by physical drift allowance
-- statement:
--   For the original BV Lévy source and any left-continuous dividend strategy, a single almost-sure BV drift-deficit event controls the whole discounted Stieltjes payout through any path-dependent cut-off σ(ω), whenever S is strictly before ruin and T<S. The bound is x+S times physical drift. Unlike the already Proved deterministic-cut-off lemma, this formulation accepts the actual ruinTime random clock without replacing it by a deterministic horizon. It preserves continuous dividend mass, ordinary right jumps and time-zero payments.
-- source:
--   Directly reuse bv_actual_levy_residual_ae_monotone_all_times and stopped_dividend_payoff_le_uncontrolled_reserve_before_ruin, both Proved. Crucially the latter is applied for the particular actual σ ω after selecting the single BV full-measure event, so no uncountable family of exceptional sets is intersected. This is a random-clock localisation envelope, not the HJB supermartingale identity.

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_stopped_dividend_payoff_le_uncontrolled_reserve_before_ruin

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave3_03_bv_surviving_random_clock_drift_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0∞)
    (T S : ℝ≥0) (hTS : T < S) :
    ∀ᵐ ω ∂P, (S : ℝ≥0∞) < ruinTime X x D ω →
      (∫⁻ r in paymentTimes (σ ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (x + (S : ℝ) * X.drift) := by sorry
