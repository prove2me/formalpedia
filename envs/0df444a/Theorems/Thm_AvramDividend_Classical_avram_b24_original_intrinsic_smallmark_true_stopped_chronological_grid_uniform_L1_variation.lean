-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_intrinsic_smallmark_true_stopped_chronological_grid_uniform_L1_variation
-- name    : AvramDividend.Classical.avram_b24_original_intrinsic_smallmark_true_stopped_chronological_grid_uniform_L1_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:45:44.479342+00:00
-- url     : https://prove2.me/theorems/697740f7-a277-4abc-b309-341c5a5fa220
-- title:
--   True original finite-activity compensated smallmark noise has one integrable total variation envelope under every bounded random ruin-clipped chronological physical grid
-- statement:
--   For the original finite-negative-jump-activity Lévy X, any intrinsic same-space compensated smallmark source Jsmall and any nondecreasing chronological deterministic physical grid with final time at most T, clip every grid endpoint at ANY original random physical time σ(ω), including the true ruin stop, by min(t_i,σ(ω)). On one common original P-conull event the total absolute Jsmall variation along the entire clipped physical grid is bounded uniformly over ALL n,t and random clipping clocks σ by exactly the same integrable original negative smallmarked Poisson count plus T times full compensator drift envelope B_T. This is a rigorous pathwise stopped physical marked-noise variation bound and a direct B219 component: clipping a monotone grid preserves monotonicity and its final time remains ≤T, so the already Proved all-chronological-grid same-noise uniform variation source applies. The theorem concerns source variation; predictability/stopping-measurability for stochastic centring is a separate B218 obligation, and no large-mark second moment, zero ν or postruin process is introduced.
-- source:
--   B24 original intrinsic marked all chronological physical grids integrable uniform variation under genuine count and true monotone clip min.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_intrinsic_smallmark_true_stopped_chronological_grid_uniform_L1_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω)))
    (T : ℝ≥0) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Ioo (-1 : ℝ) 0)
    let B : Ω → ℝ := fun ω => (N ω).toReal +
      (T : ℝ) * ‖∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν‖
    Integrable B P ∧
      ∀ᵐ ω ∂P, ∀ (n : ℕ) (t : ℕ → ℝ≥0)
        (σ : Ω → ℝ≥0), Monotone t → t n ≤ T →
        (∑ i ∈ Finset.range n,
          ‖Jsmall (min (t (i + 1)) (σ ω)) ω -
            Jsmall (min (t i) (σ ω)) ω‖) ≤ B ω := by sorry
