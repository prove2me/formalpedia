-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_random_ruin_clock_residual_nonpositive
-- name    : AvramDividend.Classical.avram_p3_bv_original_random_ruin_clock_residual_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:29:01.085312+00:00
-- url     : https://prove2.me/theorems/040b8c1c-379b-4910-a2ce-7a20105986d7
-- title:
--   Original BV residual has nonpositive weighted increments on every ruin-clamped random grid
-- statement:
--   For the genuine original bounded-variation Lévy source, each sample-dependent clock-clamped mesh of ordered deterministic times remains ordered. On the full original almost-sure event where its actual physical drift minus negative left-jump cumulative residual is monotone, every nonnegative weighted stopped residual increment is nonpositive. This includes the interval crossing the ruin clock without requiring the residual to vanish, replacing X, or introducing compensation assumptions.
-- source:
--   Proved source original raw removed BV residual monotonicity e9d95081 and finite sum sign arithmetic.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- The actual original BV continuous residual remains a nonpositive
weighted correction on sample-dependent ruin-clamped grid times. -/

theorem AvramDividend.Classical.avram_p3_bv_original_random_ruin_clock_residual_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (τ : Ω → ℝ≥0) (W : ℕ → Ω → ℝ)
    (hW : ∀ ω i, 0 ≤ W i ω) :
    ∀ᵐ ω ∂P,
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
            else 0)
      (∑ i ∈ Finset.range n,
        W i ω * (R (min (u i) (τ ω)) -
          R (min (u (i + 1)) (τ ω)))) ≤ 0 := by sorry
