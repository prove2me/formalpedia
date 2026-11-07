-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_stopped_weighted_drift_intrinsic_jump_budget
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_stopped_weighted_drift_intrinsic_jump_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:32:36.030642+00:00
-- url     : https://prove2.me/theorems/37764aa9-5686-46e0-9003-24bfdc7d3096
-- title:
--   Original stopped physical-grid BV drift source upper bound in actual intrinsic marked-jump integrals
-- statement:
--   The original bounded-variation Lévy sample path on the exact ruin/horizon stopped grid has a nonpositive weighted residual. Replacing its actual raw jump-total increments by source-exact intrinsic marked negative-jump integrals yields a same-grid drift/jump upper bound for any nonnegative state-dependent cell weights, with no stochastic surrogate.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_stopped_weighted_raw_jump_grid_budget
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_raw_negative_jump_halfopen_marked_real
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_disjoint_interval_additivity
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_stopped_weighted_drift_intrinsic_jump_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (m : ℕ)
    (W : ℕ → Ω → ℝ) (hW : ∀ ω i, 0 ≤ W i ω) :
    ∀ᵐ ω ∂P,
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let s : ℕ → ℝ≥0 := fun i =>
        min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
      let Δ : ℝ≥0 → ℝ := fun v =>
        X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
      let N : ℕ → Measure (ℝ≥0 × ℝ) := fun i =>
        ((Measure.count.restrict
          ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ Ioc (s i) (s (i + 1)))).map
            (fun v : ℝ≥0 => (v, Δ v)))
      (∑ i ∈ Finset.range (m + 1),
        W i ω * (X.X (s (i + 1)) ω - X.X (s i) ω)) ≤
      ∑ i ∈ Finset.range (m + 1),
        W i ω *
          ((((s (i + 1) : ℝ) - (s i : ℝ)) * X.drift) -
            (∫⁻ p, ENNReal.ofReal (-p.2) ∂N i).toReal) := by sorry
