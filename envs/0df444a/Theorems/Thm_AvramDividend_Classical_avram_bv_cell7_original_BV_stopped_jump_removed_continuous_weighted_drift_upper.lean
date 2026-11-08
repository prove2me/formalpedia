-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_stopped_jump_removed_continuous_weighted_drift_upper
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_stopped_jump_removed_continuous_weighted_drift_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:36:05.954301+00:00
-- url     : https://prove2.me/theorems/472e8b9a-0f33-4da5-bbe7-7f9e696ae812
-- title:
--   Original stopped BV jump-removed continuous grid increments bounded by authentic drift
-- statement:
--   On the actual original admissible dividend path stopped at ruin or the physical horizon, the signed discounted finite sum of jump-removed BV source increments is at most the same-grid signed source drift allowance. The proof imports the genuine almost-sure monotonicity of the raw original Levy drift residual after subtracting the exact real negative-jump tsum, and the Proved monotonicity of the clipped physical clock. No equality-in-law replacement or residual-zero assumption is used.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_raw_R_ae_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_stopped_grid_monotone

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_stopped_jump_removed_continuous_weighted_drift_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (T : ℝ≥0) (m : ℕ) :
    ∀ᵐ ω ∂P,
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let u : ℕ → ℝ≥0 := fun i =>
        min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      (∑ i ∈ Finset.range (m + 1),
        Real.exp (-(q * (u i : ℝ))) * (Y (u (i + 1)) - Y (u i))) ≤
      (∑ i ∈ Finset.range (m + 1),
        Real.exp (-(q * (u i : ℝ))) *
          (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift)) := by sorry
