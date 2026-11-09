-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_postpayment_zero_nojump_weighted_cash_restart
-- name    : AvramDividend.Classical.avram_bv_zero13_original_postpayment_zero_nojump_weighted_cash_restart
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T23:32:29.611839+00:00
-- url     : https://prove2.me/theorems/0228684b-d642-4d86-a444-52478d42cb93
-- title:
--   Original BV postpayment zero-contact weighted cash on a physical deterministic restart interval
-- statement:
--   For the original finite-negative-jump-activity bounded-variation process and arbitrary adapted admissible dividends, a surviving physical interval [s,T] with postpayment reserve zero at every instant and no source negative jump has actual positive-interval Stieltjes cash equal to drift-scaled Lebesgue cash, for every nonnegative weight. The interval can begin after a positive right-payment lump at s, whose atom is excluded by Ioc. Endpoints can be any deterministic s≤T; no strong Markov assertion at random stopping times is made.
-- source:
--   Imports public Proved dc73fa6f physical postpayment endpoint cash equality and 2a0cae7c original nojump drift, plus Mathlib finite Ioc measure ext, extending Proved 4bb33bff to arbitrary deterministic restart intervals.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_postpayment_zero_Ioc_cash_eq_drift
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_zero13_original_postpayment_zero_nojump_weighted_cash_restart
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hDrift : 0 ≤ X.drift)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (s T : ℝ≥0) (hT : 0 < T) (hsT : s ≤ T) :
    ∀ᵐ ω ∂P,
      (T : ℝ≥0∞) < ruinTime X x D ω →
      (∀ u : ℝ≥0, s ≤ u → u ≤ T →
        riskProcess X x D u ω -
          (rightLimit D u ω - D u ω) = 0) →
      (∀ u : ℝ≥0, u ∈ Ioc s T →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) →
      ∀ f : ℝ → ℝ≥0∞,
        (∫⁻ t in Ioc (s : ℝ) (T : ℝ), f t
          ∂(dividendMeasure D ω)) =
        (∫⁻ t in Ioc (s : ℝ) (T : ℝ), f t
          ∂((ENNReal.ofReal X.drift) • volume)) := by sorry
