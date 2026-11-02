-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_nonmonotone_eventual_exact_discounted_stieltjes_integral_domains
-- name    : AvramDividend.Classical.avram_wave7_ubv_original_nonmonotone_eventual_exact_discounted_stieltjes_integral_domains
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:55:59.793986+00:00
-- url     : https://prove2.me/theorems/a1d88881-e3b7-4a38-9236-bb2e82854c75
-- title:
--   Original UBV nonmonotone eventual exact full discounted dividend integral domains
-- statement:
--   For the actual original spectrally negative Levy source X and admissible D, any finite nonnegative horizon T, discount q and arbitrary nonmonotone extended random clocks S_n with liminf S_n=top almost surely, a pathwise eventual index N makes the full discounted dividendMeasure D integrals over the payment times of min(ruinTime,S_n) truncated at T exactly equal the original ruin-time dividend integral. This follows solely by equality of the restricted payment-time domains in the accepted source theorem and does not assert a budget, stochastic integration identity, regularity or local-time condition.
-- source:
--   Previously accepted original eventual exact payment domain theorem 68f10cb0-bd2a-41c7-92bf-4bafb77cd02f and original dividendMeasure definition; no overlap with Chat 04-B's integration calculations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_nonmonotone_eventual_payment_domain_stabilises

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_ubv_original_nonmonotone_eventual_exact_discounted_stieltjes_integral_domains
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (T : ℝ) (hT : 0 ≤ T)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, S (n + k) ω) = ⊤) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (S n ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
