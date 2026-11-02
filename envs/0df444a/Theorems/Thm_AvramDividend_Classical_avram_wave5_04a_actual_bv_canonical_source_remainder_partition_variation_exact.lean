-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_canonical_source_remainder_partition_variation_exact
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_canonical_source_remainder_partition_variation_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:34:47.245328+00:00
-- url     : https://prove2.me/theorems/3ddc1a4c-7733-4bfe-82ec-284764e67394
-- title:
--   Actual BV source canonical downward residual has exact finite-partition total variation
-- statement:
--   For the genuine original spectrally negative Levy process of bounded variation, construct on a single full-probability event the explicit residual function R(t)=t*source drift-X_t minus the complete real magnitude sum of all original negative source left jumps up to t. R is nondecreasing, and for every monotone original time partition its sum of absolute increments is exactly R(final)-R(initial), making the remaining downward component a coherent finite-variation path with a sharp variation identity. No pure-jump equality or stochastic chain rule is invoked.
-- source:
--   Wave5 Chat04-A; direct real pathwise consequence of canonical monotone original BV remainder child 019edf01-4961-4bf1-805e-b935366106bb and Finset.sum_range_sub; submit only after that child's Proved verdict.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_canonical_remainder_monotone

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Exact total finite-partition variation of the canonical downward source
residual path, for any original BV sample and any ordered time partition. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_canonical_source_remainder_partition_variation_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (u : ℝ≥0),
            if 0 < u ∧ u ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ),
        (Finset.range n).sum
          (fun i => |R (u (i + 1)) - R (u i)|) =
        R (u n) - R (u 0) := by sorry
