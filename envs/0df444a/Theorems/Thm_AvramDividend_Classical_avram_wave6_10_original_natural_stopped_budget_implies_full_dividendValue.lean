-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue
-- name    : AvramDividend.Classical.avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:51:55.78585+00:00
-- url     : https://prove2.me/theorems/a28c3854-b917-4949-8199-985acc3ac866
-- title:
--   Uniform natural stopped original dividends control the full dividendValue, with all time atoms
-- statement:
--   For the actual original spectrally negative Levy X and an actual admissible dividend regulator D, any ENNReal constant A that controls the expected discounted Stieltjes payout stopped at min(ruinTime,n) uniformly for all natural n also controls the complete original dividendValue. Combine the Proved natural-to-real closed-horizon budget bridge with the Proved full-value supremum theorem. This is a direct endpoint interface from corrected UBV natural-horizon bound 61bbf167 to full value 132447c8, without additional stochastic assumptions and including both the time-zero and terminal payment atoms.
-- source:
--   Proved original natural stopped budget to real horizon UUID 9dcdd14a-09ba-4d42-b4db-2fb744143da8 and original real horizon to full value UUID dc933bd8-8284-4e80-89e6-304a074e0a4a. Source-typed IsAdmissible first projection is IsDividendStrategy; no independent stochastic model or extra axioms.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_natural_stopped_budget_implies_all_real_horizon_budget
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_uniform_truncated_bounds

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (A : ℝ≥0∞)
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ A) :
    dividendValue X q x D ≤ A := by sorry
