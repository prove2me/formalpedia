-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_all_unbounded_of_near_zero_path_decrease
-- name    : AvramDividend.Classical.zero_cap_value_upper_bound_all_unbounded_of_near_zero_path_decrease
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:34:26.885514+00:00
-- url     : https://prove2.me/theorems/ddb2ff46-b949-4260-8374-9ad38d4dbba9
-- title:
--   All-reserve zero-cap verification from local decreases of unbounded-variation Lévy paths
-- statement:
--   Under the standing assumptions and unbounded variation, suppose almost every Levy sample path strictly decreases between two times arbitrarily near time zero. Then the zero-barrier reflected process ruins instantly almost surely, and the zero-barrier candidate dominates the capped optimal dividend value at every nonnegative reserve. This criterion requires only local path decreases, a more natural bridge to unbounded sample-path variation than local negativity relative to the original starting value.
-- source:
--   Pathwise near-zero-decrease-to-ruin theorem 1951669a-79ea-4230-bef0-b4758495947c (submitted), and canonically Proved global instantaneous-ruin zero-cap verification theorem d7ea5cfe-8091-453c-ae72-62b42d5b18ca.

import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_near_zero_path_decrease
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_all_unbounded_of_instant_ruin

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.zero_cap_value_upper_bound_all_unbounded_of_near_zero_path_decrease
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hnbv : ¬ X.BoundedVariation)
    (hDecrease : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s t : ℝ≥0, s ≤ t ∧ t < ε ∧ X.X t ω < X.X s ω) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q 0 x ≤ ENNReal.ofReal (barrierValue W 0 x) := by sorry
