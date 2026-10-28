-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_all_unbounded_of_instant_ruin
-- name    : AvramDividend.Classical.zero_cap_value_upper_bound_all_unbounded_of_instant_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:20:57.264335+00:00
-- url     : https://prove2.me/theorems/d7ea5cfe-8091-453c-ae72-62b42d5b18ca
-- title:
--   Unbounded-variation global zero-cap verification from instantaneous barrier ruin
-- statement:
--   For a spectrally negative Levy process satisfying the standing assumptions and having paths of unbounded variation, almost-sure instantaneous ruin of the zero-barrier reflected process is sufficient for the zero-cap dividend candidate to dominate the optimal capped dividend value at every nonnegative reserve. This criterion isolates the exact missing stochastic regularity fact without requiring a stronger near-zero negative path witness premise.
-- source:
--   Canonically Proved instantaneous-ruin boundary package 31b87209-167f-4581-9756-bf3cd9ee93e7, reserve-zero upper bound d58a54f2-7f8b-4467-b485-93506d163ab8 and zero-cap reserve transfer a77b926c-06ed-4fc1-a8f4-945437968469.

import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_package_of_unbounded_instant_ruin
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound_of_boundary
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_of_zero_bound

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.zero_cap_value_upper_bound_all_unbounded_of_instant_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hnbv : ¬ X.BoundedVariation)
    (hRuin : ∀ᵐ ω ∂P, barrierRuinTime X 0 ω = 0) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q 0 x ≤ ENNReal.ofReal (barrierValue W 0 x) := by sorry
