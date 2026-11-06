-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_strategywise_cofinal_vanishing_strict_real_values
-- name    : AvramDividend.Classical.avram_limit2_strategywise_cofinal_vanishing_strict_real_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:04:03.938591+00:00
-- url     : https://prove2.me/theorems/7626cfbc-b9b5-4d9a-ad57-c34782f3bde7
-- title:
--   Strategywise arbitrary cofinal strict vanishing terminal budgets bound all original real capped/top dividends
-- statement:
--   Every original positive reserve x and capped admissible dividend strategy D may choose its own cofinal real deterministic horizon family T and its own nonnegative error→0. If each stopped strict original discounted Stieltjes cash plus nonnegative terminal expectation is ≤w(x)+error_k, then its actual perpetual value is finite, real perpetual cash is integrable and exactly matches the ENNReal value, the real mean is ≤w(x), and all capped plus C=top unrestricted original values satisfy the source upper bound. Endpoint/time-zero atoms remain preserved; no terminal vanishing, equality-in-law, axioms or circular canonical proof.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_cofinal_vanishing_strict_cash_real_perpetual
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_strategywise_cofinal_vanishing_strict_real_values
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C → 0 ≤ w x)
    (hSource : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        ∃ T : ℕ → ℝ,
          (∀ a : ℝ, ∃ k : ℕ, a ≤ T k) ∧
          ∃ error : ℕ → ℝ≥0∞,
            (∀ ε : ℝ≥0, 0 < ε →
              ∃ N : ℕ, ∀ k : ℕ, N ≤ k → error k ≤ (ε : ℝ≥0∞)) ∧
            (∀ k : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
              (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
                Iio (T k),
                ENNReal.ofReal (Real.exp (-(q * t)))
                  ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤
                ENNReal.ofReal (w x) + error k)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        Integrable (fun ω : Ω =>
          ∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
        dividendValue X q x D =
          ENNReal.ofReal (∫ ω,
            (∫ t in paymentTimes (ruinTime X x D ω),
              Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ∧
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ w x) ∧
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
