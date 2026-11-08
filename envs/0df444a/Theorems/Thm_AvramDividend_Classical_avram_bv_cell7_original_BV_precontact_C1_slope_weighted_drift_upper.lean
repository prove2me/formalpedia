-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_precontact_C1_slope_weighted_drift_upper
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_precontact_C1_slope_weighted_drift_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:36:18.211705+00:00
-- url     : https://prove2.me/theorems/2c751dd4-17b8-4125-b72f-117537ff2973
-- title:
--   Original stopped physical BV C1 drift bound requiring positive slopes only strictly before the ruin or horizon contact
-- statement:
--   The actual bounded-variation SpectrallyNegativeLevy process and admissible dividend path have an almost-sure discounted value-slope-weighted jump-removed drift bound on every genuine ruin/horizon clipped physical grid. Source derivative nonnegativity is required only for cells whose left endpoint is strictly before the clipped ruin/horizon time. The Proved original flat-after-contact theorem makes every later cell exactly zero, including any arbitrary slope at the ruin boundary. The original signed negative-jump tsum and nonzero monotone residual remain intact.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_raw_R_ae_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_stopped_grid_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_physical_flat_after_contact

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_precontact_C1_slope_weighted_drift_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ m : ℕ,
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let u : ℕ → ℝ≥0 := fun i =>
        min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      let z : ℕ → ℝ := fun i =>
        x + X.X (u i) ω - rightLimit D (u i) ω
      (∀ i ∈ Finset.range (m + 1), u i < τ → 0 ≤ deriv w (z i)) →
      (∑ i ∈ Finset.range (m + 1),
        (Real.exp (-(q * (u i : ℝ))) * deriv w (z i)) *
          (Y (u (i + 1)) - Y (u i))) ≤
      (∑ i ∈ Finset.range (m + 1),
        (Real.exp (-(q * (u i : ℝ))) * deriv w (z i)) *
          (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift)) := by sorry
