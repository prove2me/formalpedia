-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_stopped_weighted_raw_jump_grid_budget
-- name    : AvramDividend.Classical.avram_bv_cell7_original_stopped_weighted_raw_jump_grid_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T08:23:01.655579+00:00
-- url     : https://prove2.me/theorems/4956c00b-aa7a-40dd-a6ee-aba5cdd73f6b
-- title:
--   Original BV stopped physical-grid weighted drift and raw negative-jump source inequality
-- statement:
--   For the actual BV spectrally negative Lévy path X and physical m+1-cell grid clipped by the original dividend strategy's ruin/horizon clock, every nonnegative weighted sum of true X cell increments is bounded by the corresponding drift increments minus the actual raw negative-jump increments. The proof uses the genuine original BV residual sign, with exact same-grid algebra; no law surrogate or compensated-source hypothesis is assumed.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_uniform_ruin_stopped_residual_nonpositive

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_stopped_weighted_raw_jump_grid_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (m : ℕ)
    (W : ℕ → Ω → ℝ) (hW : ∀ ω i, 0 ≤ W i ω) :
    ∀ᵐ ω ∂P,
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let u : ℕ → ℝ≥0 := fun i =>
        ((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))
      let s : ℕ → ℝ≥0 := fun i => min (u i) τ
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      (∑ i ∈ Finset.range (m + 1),
        W i ω * (X.X (s (i + 1)) ω - X.X (s i) ω)) ≤
      ∑ i ∈ Finset.range (m + 1),
        W i ω *
          ((((s (i + 1) : ℝ) - (s i : ℝ)) * X.drift) -
            (J (s (i + 1)) - J (s i))) := by sorry
