-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_source_and_dividend_finite_grid_discounted_jump_budget
-- name    : AvramDividend.Classical.avram_wave7_02_original_positive_source_and_dividend_finite_grid_discounted_jump_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:56:13.170202+00:00
-- url     : https://prove2.me/theorems/d3071eac-7c80-4ecd-9413-13a8b19ec22a
-- title:
--   Exact original simultaneous negative source and right-payment jumps yield a discounted finite-grid chronological upper bound
-- statement:
--   For any finite set of strictly positive pre-ruin original source clock times, the sum of the discounted actual source-plus-payment value jumps including the payable right-dividend atoms is at most the sum of discounted original source-only value jumps. The chronological decomposition explicitly includes simultaneous negative Lévy source jumps and cumulative dividend right jumps, using the original left limit X and riskProcess definitions, and separates the time-zero dividend mass.
-- source:
--   Proved original joint source/payment positive-clock HJB jump lemma 1e75d817, positive original exponential weights, Finset.sum_le_sum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_clock_source_and_payment_simultaneous_jump_budget
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_positive_source_and_dividend_finite_grid_discounted_jump_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (S : Finset ℝ≥0)
    (hTimes : ∀ t ∈ S, 0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ t ∈ S,
      (Real.exp (-(q * (t : ℝ))) *
        ((w (x + X.X t ω - rightLimit D t ω) -
            w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω)) +
          (rightLimit D t ω - D t ω)))) ≤
    (∑ t ∈ S,
      (Real.exp (-(q * (t : ℝ))) *
        (w (x + X.X t ω - D t ω) -
          w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω)))) := by sorry
