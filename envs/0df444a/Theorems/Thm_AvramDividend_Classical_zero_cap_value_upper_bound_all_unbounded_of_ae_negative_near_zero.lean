-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_all_unbounded_of_ae_negative_near_zero
-- name    : AvramDividend.Classical.zero_cap_value_upper_bound_all_unbounded_of_ae_negative_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:13:52.749983+00:00
-- url     : https://prove2.me/theorems/75bcce68-4d32-4a34-a7be-feeef744f038
-- title:
--   Unbounded-variation zero-cap dividend upper bound at all reserves under near-zero downward regularity
-- statement:
--   If an unbounded-variation spectrally negative Levy process satisfies the standing hypotheses and its paths almost surely attain negative values arbitrarily near time zero, the zero-barrier candidate is an upper bound on the admissible dividend value from every nonnegative reserve. This extends the proven instantaneous-ruin boundary identity to the whole state space using the proven zero-cap reserve transfer principle. It covers unbounded-variation pure-jump processes alongside Gaussian models, conditional on the path-regularity hypothesis.
-- source:
--   Canonically Proved unbounded near-zero boundary package fd11e610-82a7-4259-aadf-65c9d68662bb, reserve-zero upper bound d58a54f2-7f8b-4467-b485-93506d163ab8, and all-reserves transfer a77b926c-06ed-4fc1-a8f4-945437968469.

import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_package_of_unbounded_ae_negative_near_zero
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound_of_boundary
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_of_zero_bound

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.zero_cap_value_upper_bound_all_unbounded_of_ae_negative_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hnbv : ¬ X.BoundedVariation)
    (hNear : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q 0 x ≤ ENNReal.ofReal (barrierValue W 0 x) := by sorry
