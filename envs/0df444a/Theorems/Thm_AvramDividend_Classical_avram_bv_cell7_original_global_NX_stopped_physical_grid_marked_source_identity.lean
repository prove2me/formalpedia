-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_global_NX_stopped_physical_grid_marked_source_identity
-- name    : AvramDividend.Classical.avram_bv_cell7_original_global_NX_stopped_physical_grid_marked_source_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:21:28.577448+00:00
-- url     : https://prove2.me/theorems/2d4786aa-d3ba-471a-9027-2ea78f187b7e
-- title:
--   Original global Lévy jump measure equals intrinsic stopped marked source on every physical cell
-- statement:
--   For the actual Lévy sample path, arbitrary measurable nonnegative marked-source integrals on the original global jump measure restricted to the exact ruin/horizon stopped interval equal both the intrinsic restricted original jump measure integral and the genuine finite stopped physical-grid jump-time series, with time zero excluded and the final contact cell retained. The bridge uses the accepted original global and half-open count-to-tsum theorems and physical-grid partition.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_stopped_jump_count_source_eq_tsum
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_halfopen_physical_cell_marked_nonlinear_count_tsum
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_stopped_marked_grid_exact_jump_time_tsum

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_global_NX_stopped_physical_grid_marked_source_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (m : ℕ) (ω : Ω)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
    let Δ : ℝ≥0 → ℝ := fun v =>
      X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
        (fun v : ℝ≥0 => (v, Δ v)))
    let N : Set ℝ≥0 → Measure (ℝ≥0 × ℝ) := fun I =>
      (Measure.count.restrict ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ I)).map
        (fun v : ℝ≥0 => (v, Δ v))
    u 0 = 0 ∧ u (m + 1) = min T τ ∧
      (∫⁻ p, (if p.1 ∈ Ioc (u 0) (u (m + 1)) then F p else 0) ∂NX) =
        (∫⁻ p, F p ∂N (Ioc (u 0) (u (m + 1)))) ∧
      (∫⁻ p, (if p.1 ∈ Ioc (u 0) (u (m + 1)) then F p else 0) ∂NX) =
        ∑ i ∈ Finset.range (m + 1),
          (∑' v : ℝ≥0,
            if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
              F (v, Δ v) else 0) := by sorry
