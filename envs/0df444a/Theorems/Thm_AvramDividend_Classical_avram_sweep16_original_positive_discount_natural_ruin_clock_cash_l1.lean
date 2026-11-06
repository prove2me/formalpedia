-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_positive_discount_natural_ruin_clock_cash_l1
-- name    : AvramDividend.Classical.avram_sweep16_original_positive_discount_natural_ruin_clock_cash_l1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:16:50.3401+00:00
-- url     : https://prove2.me/theorems/66304b93-c348-4066-81a9-43134b04d139
-- title:
--   Original positive-discount natural ruin-clock full-Stieltjes cash is integrable without UI hypotheses
-- statement:
--   On the unaltered original spectrally negative Levy probability space, admissible dividend strategy and original natural bounded ruin clock, the real part of exact closed-boundary discounted dividend cash is L1 for every q>0. Source exact: choose a small positive Esscher tilt with psi(theta)<q using the proved Levy exponent theorem, and invoke the proved original random upper-clock theta cash L1 theorem. Includes time-zero and right-payment atoms; no stopped Ito residual or uniform-integrability premise.
-- source:
--   Original natural finite ruin clock in canonical 750ad13b. Proved source 6b7f5580 small Esscher tilt and 006d9506 original random-clock full-Stieltjes cash L1.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_source_psi_positive_small_tilt_below_any_positive_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_unbounded_random_clock_stieltjes_cash_integrable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_sweep16_original_positive_discount_natural_ruin_clock_cash_l1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ))) :
    Integrable (fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P := by sorry
