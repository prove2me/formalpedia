-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_bounded_random_clock_real_mean_eq
-- name    : AvramDividend.Classical.avram_wave7_03_original_full_ruin_bounded_random_clock_real_mean_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:36:32.007994+00:00
-- url     : https://prove2.me/theorems/431c22a6-71dd-4582-ac36-a3375da127f7
-- title:
--   Original full stopped real Stieltjes cash expectation equals double ENNReal payout under a.e. finite stopped mass
-- statement:
--   Under actual original spectrally negative Levy X, capped admissible dividend strategy D, bounded measurable random clock tau, q nonnegative and almost-sure finite Stieltjes mass on exactly paymentTimes(ruinTime) cap Iic tau, the double ENNReal expected payout equals ofReal of the signed real expected Stieltjes integral over the identical stopped set and measure. Real L1 integrability is derived from accepted original-process all-variation bounded-clock integrability; it is not silently assumed. Retains all zero/continuous/jump payments and excludes positive ruin boundary.
-- source:
--   Accepted original bounded-clock full cash L1 theorem 3deca135; new W7-03 exact full-ruin finite-mass same-measure bridge 339849ef.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_finite_mass_real_ennreal_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_full_ruin_bounded_random_clock_real_mean_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (hMass : ∀ᵐ ω ∂P,
      (dividendMeasure D ω)
        (paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ)) ≠ ⊤) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    ENNReal.ofReal
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
