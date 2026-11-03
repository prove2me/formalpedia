-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_allvariation_bounded_strict_random_clock_real_ennreal_mean_eq
-- name    : AvramDividend.Classical.avram_wave7_03_original_allvariation_bounded_strict_random_clock_real_ennreal_mean_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:22:18.024374+00:00
-- url     : https://prove2.me/theorems/8595a346-461a-49ae-bb65-c033e34cd4d8
-- title:
--   Original all-variation bounded strict-pre-ruin real Stieltjes expected cash equals double ENNReal payout
-- statement:
--   Under exactly the actual spectrally negative Lévy process and capped admissible dividend strategy, for every bounded measurable original random clock τ which is zero or strictly before ruin almost surely, the expected complete discounted Stieltjes cash on the chronological real interval [0,τ] embeds exactly into the original double-ENNReal stopped dividend expectation. There is no BV/UBV or standing assumption: real L1 integrability follows from the already accepted general original bounded-random-clock cash theorem and pointwise same-measure equality, then the original random-clock expectation bridge yields the identity. Initial atom, all interior jumps, continuous and singular-continuous payments are retained, positive ruin boundary cash is excluded.
-- source:
--   General original bounded random clock Stieltjes cash integrability 3deca135; accepted W7-03 pathwise strict-prefix equality 2b209825; W7-03 random-clock expectation equality 59216c01. Same process Ω,P,X,D,ruinTime; no HJB premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_strict_preruin_closed_real_ennreal_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_strict_preruin_random_clock_real_mean_to_ennreal

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_allvariation_bounded_strict_random_clock_real_ennreal_mean_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
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
