-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
-- name    : AvramDividend.Classical.avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:46:41.960567+00:00
-- url     : https://prove2.me/theorems/fc7c1b8a-c416-450c-b1ad-cadf9344888f
-- title:
--   Unconditional complete original ruin-stopped expected real/ENNReal Stieltjes bridge for all variations and bounded clocks
-- statement:
--   For the original spectrally negative Levy process X, original capped admissible dividend D, q≥0 and bounded measurable random time tau, the full ruin-stopped double-ENNReal dividend expectation equals ENNReal.ofReal of the expected real discounted Stieltjes integral over exactly paymentTimes(ruinTime) cap Iic tau against exactly dividendMeasure D. No BV/UBV, no strict-pre-ruin condition, no extra integrability or finite-mass premise: finiteness follows from paymentTimes subset Icc 0 tau and the accepted exact mass-to-rightLimit formula, and integrability follows from accepted original bounded-clock L1 theorem via the proved conditional full mean bridge. Includes time-zero right-limit atom, continuous/singular continuous and jumps, excludes positive ruin boundary.
-- source:
--   Accepted mass formula d6ace15b and new accepted W7-03 full random-clock signed/ENNReal expected bridge 431c22a6. Same canonical objects, no altered process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_bounded_random_clock_real_mean_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ))) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    ENNReal.ofReal
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
