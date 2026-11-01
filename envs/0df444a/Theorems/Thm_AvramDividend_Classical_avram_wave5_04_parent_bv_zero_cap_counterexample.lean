-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04_parent_bv_zero_cap_counterexample
-- name    : AvramDividend.Classical.avram_wave5_04_parent_bv_zero_cap_counterexample
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T01:21:50.305795+00:00
-- url     : https://prove2.me/theorems/c4bc3559-e543-4e60-a052-fd6eca321c1a
-- title:
--   Original BV parent fails at zero cap via a genuine zero-barrier initial atom
-- statement:
--   For every actually existing spectrally negative Levy source satisfying the standing BV assumptions and any positive initial reserve, the unchanged original zero-barrier strategy is admissible at cap zero. The identically zero candidate w satisfies all analytic and terminal premises of the legacy uncorrected bounded-variation stochastic verification parent, because the strict interior (0,C) is empty. Nevertheless the complete original discounted Stieltjes dividend integral at horizon T=0 equals the strictly positive initial capital, contradicting its claimed upper bound zero. This is a conditional counterexample uniformly for any such genuine BV source, not a construction of an existence witness for the source. It explains why the legacy parent cannot follow from the corrected positive-cap core.
-- source:
--   Legacy parent 65617e0a-5e27-4272-bb37-8905da7da981; Proved original barrier admissibility 32b4ccb8, barrier initial Stieltjes atom f5167fe3, dividend singleton 4f229f9a and exact time-zero payout 50183965. The source and probability remain the original X, P and filtration; no Poisson-copy model and no atomic approximation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_initial_dividendMeasure_atom_formula
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_truncated_dividend_payoff_at_zero_eq_initial_atom

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04_parent_bv_zero_cap_counterexample
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q x : ℝ) (hq : 0 < q) (hx : 0 < x) :
    ∃ (w : ℝ → ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (T : ℝ),
      ContinuousOn w (Ici 0) ∧
      (∀ y < 0, w y = 0) ∧
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) ∧
      IsAdmissibleLe X x C D ∧
      (∀ ω (t : ℝ≥0), 0 < t →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ w (riskProcess X x D t ω)) ∧
      0 ≤ T ∧
      ¬ ((∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x)) := by sorry
