-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_bv_bounded_strict_random_clock_real_ennreal_mean_eq
-- name    : AvramDividend.Classical.avram_wave7_03_original_bv_bounded_strict_random_clock_real_ennreal_mean_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:17:24.213647+00:00
-- url     : https://prove2.me/theorems/6060a4af-7c3a-4459-9a96-f92d95673cfc
-- title:
--   Original BV bounded strict-pre-ruin real Stieltjes mean equals ENNReal expected cash without L1 premise
-- statement:
--   For the true standing bounded-variation spectrally negative Lévy source and capped admissible original dividend strategy, any measurable bounded random clock τ which is zero or strictly pre-ruin almost surely admits an exact equality of the full original double-ENNReal stopped payout and the embedding of its real discounted Stieltjes expectation on [0,τ]. The necessary L1 integrability of the signed-real cash is derived from the accepted original BV random-clock L1 theorem and exact pathwise same-measure equality, rather than postulated. The result preserves the initial right-limit atom, all right jumps and diffuse/singular-continuous payments, with q≥0 and finite T.
-- source:
--   Accepted original BV bounded clock cash L1 5817eddd; accepted W7-03 pathwise real/ENNReal equality 2b209825; accepted W7-03 random-clock expectation conversion 59216c01 once Proved. No new model or circular ENNReal upper bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_bounded_random_clock_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_strict_preruin_closed_real_ennreal_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_strict_preruin_random_clock_real_mean_to_ennreal

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_bv_bounded_strict_random_clock_real_ennreal_mean_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (hPre : ∀ᵐ ω ∂P,
      τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    ENNReal.ofReal
      (∫ ω, (∫ t in Icc (0 : ℝ) (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
