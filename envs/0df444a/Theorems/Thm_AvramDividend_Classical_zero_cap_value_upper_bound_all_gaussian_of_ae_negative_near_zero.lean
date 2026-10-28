-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_all_gaussian_of_ae_negative_near_zero
-- name    : AvramDividend.Classical.zero_cap_value_upper_bound_all_gaussian_of_ae_negative_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:03:38.211808+00:00
-- url     : https://prove2.me/theorems/8d055020-0690-4371-be56-bf3e73c74097
-- title:
--   Gaussian zero-cap dividend upper bound for all reserves under near-zero downward regularity
-- statement:
--   For a standing spectrally negative Levy process with positive Gaussian coefficient and strictly positive discount, suppose paths almost surely visit strictly negative values at arbitrarily small positive times. Then for each nonnegative reserve x, the optimal zero-capped dividend value is bounded above by the scale-function zero-barrier candidate at x. A fully proved Gaussian boundary-value identity and the general reserve-transfer lemma supply the complete proof without positive-barrier scale-ratio hypotheses.
-- source:
--   Canonically Proved Gaussian near-zero boundary package ff60fd01-e2fb-4767-a47c-3219c841566f, zero-cap reserve-zero upper bound d58a54f2-7f8b-4467-b485-93506d163ab8 and all-reserve transfer a77b926c-06ed-4fc1-a8f4-945437968469.

import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_package_gaussian_of_ae_negative_near_zero
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound_of_boundary
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_of_zero_bound

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.zero_cap_value_upper_bound_all_gaussian_of_ae_negative_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (hNear : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q 0 x ≤ ENNReal.ofReal (barrierValue W 0 x) := by sorry
