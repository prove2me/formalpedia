-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_physical_residual_intrinsic_marked_cell_identity
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_physical_residual_intrinsic_marked_cell_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:47:17.244089+00:00
-- url     : https://prove2.me/theorems/71cd4e89-30a3-4796-92db-5cf2b82678bc
-- title:
--   Exact original stopped BV residual sum as physical increments, drift, and intrinsic marked negative jumps
-- statement:
--   The original BV Lévy path has an exact cumulative raw jump residual. On the original ruin/horizon stopped physical grid, the weighted residual difference in the canonical P3-GRID4 witness is precisely the original Lévy increment minus original deterministic drift plus the actual intrinsic negative-jump lintegral on that same cell. The equality holds for arbitrary original path-dependent real weights and retains the final contact cell.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_raw_negative_jump_halfopen_marked_real
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_disjoint_interval_additivity
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_physical_residual_intrinsic_marked_cell_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (m : ℕ)
    (W : ℕ → Ω → ℝ) :
    ∀ᵐ ω ∂P,
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let s : ℕ → ℝ≥0 := fun i =>
        min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
      let R : ℝ≥0 → ℝ := fun t => ((t : ℝ) * X.drift - X.X t ω) - J t
      let Δ : ℝ≥0 → ℝ := fun v =>
        X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
      let N : ℕ → Measure (ℝ≥0 × ℝ) := fun i =>
        ((Measure.count.restrict
          ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ Ioc (s i) (s (i + 1)))).map
            (fun v : ℝ≥0 => (v, Δ v)))
      (∑ i ∈ Finset.range (m + 1),
        W i ω * (R (s i) - R (s (i + 1)))) =
      ∑ i ∈ Finset.range (m + 1),
        W i ω *
          ((X.X (s (i + 1)) ω - X.X (s i) ω) -
            (((s (i + 1) : ℝ) - (s i : ℝ)) * X.drift) +
            (∫⁻ p, ENNReal.ofReal (-p.2) ∂N i).toReal) := by sorry
