-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_postpayment_zero_nojump_weighted_cash_prefix
-- name    : AvramDividend.Classical.avram_bv_zero13_original_postpayment_zero_nojump_weighted_cash_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T23:14:32.020913+00:00
-- url     : https://prove2.me/theorems/4bb33bff-2689-41a5-a99e-601976156ce9
-- title:
--   Actual postpayment-zero original BV continuous discounted Stieltjes cash, including starts after right-payment lump
-- statement:
--   On the same original bounded-variation spectrally negative Levy process and arbitrary adapted admissible D, if the postpayment controlled reserve is zero throughout an actually surviving no-negative-jump prefix, actual positive-time Stieltjes cash agrees with drift-scaled Lebesgue cash for every nonnegative discount weight. A positive initial right dividend paying the prepayment reserve down to zero is allowed and is excluded from the positive-time Ioc integral, so it must be accounted separately by the canonical initial atom ledger. This is a deterministic-clock prefix event almost surely and does not assert a strong Markov random restart theorem.
-- source:
--   Public Proved dc73fa6f postpayment restart interval cash, 2a0cae7c original no-jump drift, 7ba7a474 Ioc measure uniqueness. Strict physical survival and all-time postpayment zero are explicit hypotheses.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_postpayment_zero_Ioc_cash_eq_drift
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
import Theorems.Thm_AvramDividend_Classical_measure_restrict_Ioc_eq_of_local_Ioc_agreement
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_zero13_original_postpayment_zero_nojump_weighted_cash_prefix
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hDrift : 0 ≤ X.drift)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P,
      (T : ℝ≥0∞) < ruinTime X x D ω →
      (∀ u : ℝ≥0, u ≤ T →
        riskProcess X x D u ω -
          (rightLimit D u ω - D u ω) = 0) →
      (∀ u : ℝ≥0, u ∈ Ioc (0 : ℝ≥0) T →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) →
      ∀ f : ℝ → ℝ≥0∞,
        (∫⁻ t in Ioc (0 : ℝ) (T : ℝ), f t
          ∂(dividendMeasure D ω)) =
        (∫⁻ t in Ioc (0 : ℝ) (T : ℝ), f t
          ∂((ENNReal.ofReal X.drift) • volume)) := by sorry
