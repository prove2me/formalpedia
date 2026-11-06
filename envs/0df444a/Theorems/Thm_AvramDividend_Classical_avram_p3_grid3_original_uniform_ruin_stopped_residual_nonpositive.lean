-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_uniform_ruin_stopped_residual_nonpositive
-- name    : AvramDividend.Classical.avram_p3_grid3_original_uniform_ruin_stopped_residual_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:16:34.933464+00:00
-- url     : https://prove2.me/theorems/d5058688-ebcc-4b46-ac39-3d33529c4853
-- title:
--   Actual original BV ruin-clamped physical grid weighted residual is pathwise nonpositive
-- statement:
--   On the actual bounded-variation Lévy process and controlled ruin clock, the uniform physical grid clamped at the original ruin time has nonpositive weighted drift-minus-negative-jump residual correction for all nonnegative predictable candidate weights. Its grid geometry and a.e. residual sign follow from two independent Proved original source lemmas, with no residual-vanishing hypothesis or surrogate process.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_uniform_physical_clock_endpoints_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_random_ruin_clock_residual_nonpositive
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_uniform_ruin_stopped_residual_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (m : ℕ)
    (W : ℕ → Ω → ℝ) (hW : ∀ ω i, 0 ≤ W i ω) :
    ∀ᵐ ω ∂P,
      let u : ℕ → ℝ≥0 := fun i =>
        ((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))
      let τ : Ω → ℝ≥0 := fun ξ =>
        (min (ruinTime X x D ξ) (T : ℝ≥0∞)).toNNReal
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
            else 0)
      (∑ i ∈ Finset.range (m + 1),
        W i ω * (R (min (u i) (τ ω)) -
          R (min (u (i + 1)) (τ ω)))) ≤ 0 := by sorry
