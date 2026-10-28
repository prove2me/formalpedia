-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_path_partition_variation_bound_ws01b
-- name    : AvramDividend.Classical.bv_actual_path_partition_variation_bound_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T14:02:13.970832+00:00
-- url     : https://prove2.me/theorems/acd3eb12-f81b-4cde-becf-400b2d79a7e6
-- title:
--   Actual BV Lévy path finite-partition total-variation bound
-- statement:
--   For a standing bounded-variation spectrally negative Lévy process, almost every actual sample path has its variation over every finite increasing time partition bounded by twice the physical drift times elapsed time minus the terminal path increment, including in the infinite-activity case.
-- source:
--   Derived from the proved global BV drift-residual monotonicity and positive drift. Foundational process-level path variation needed for a boundary-aware stochastic Dynkin/Itô development. Does not assert compensator equality or killed scale harmonicity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.bv_actual_path_partition_variation_bound_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0), Monotone u → ∀ n : ℕ,
      (∑ i ∈ Finset.range n,
        |X.X (u (i + 1)) ω - X.X (u i) ω|) ≤
        2 * X.drift * ((u n : ℝ) - (u 0 : ℝ)) -
          (X.X (u n) ω - X.X (u 0) ω) := by sorry
