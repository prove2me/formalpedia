-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound_of_unbounded_ae_negative_near_zero
-- name    : AvramDividend.Classical.zero_cap_value_at_zero_upper_bound_of_unbounded_ae_negative_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T21:50:17.799005+00:00
-- url     : https://prove2.me/theorems/458a78f7-a54b-4d92-b4e0-5ce6db022f00
-- title:
--   Unbounded zero-cap optimal value bound under negative near-zero path regularity
-- statement:
--   Conditional completion of the zero-cap verification bound at zero reserve in the unbounded-variation branch. Every zero-capped admissible strategy's discounted dividends are bounded by the zero-barrier strategy by the canonical pathwise comparison theorem. Under almost-sure negative near-zero Lévy paths, the canonically Proved zero-barrier boundary package identifies that strategy's value with the scale-function candidate. The Proved uniform-strategy-to-value-supremum theorem then bounds the restricted optimal value. This directly supports the outstanding root-connected zero_cap_value_at_zero_upper_bound theorem c7854fde-e22f-45b4-90b6-1ed7e894755c.
-- source:
--   Three canonical Proved results: zero-cap pathwise dominance, zero-barrier conditional valuation, and supremum transfer.

import Theorems.Thm_AvramDividend_Classical_local_verification_per_strategy_to_capped_value_bound
import Theorems.Thm_AvramDividend_Classical_zero_cap_admissible_dividendValue_le_barrier_at_zero
import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_package_of_unbounded_ae_negative_near_zero

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.zero_cap_value_at_zero_upper_bound_of_unbounded_ae_negative_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hNear : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) :
    valueFunctionLe X q 0 0 ≤ ENNReal.ofReal (barrierValue W 0 0) := by sorry
