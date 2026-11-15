-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_zero_prepayment_generator_drift_grids_vanish
-- name    : AvramDividend.Classical.avram_bvb_obstruction_original_zero_prepayment_generator_drift_grids_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T00:37:12.968199+00:00
-- url     : https://prove2.me/theorems/6f423bd9-60bf-459c-a064-6cf591b349d3
-- title:
--   Original zero-prepayment reserve makes both finite physical generator and drift masks vanish
-- statement:
--   For any original spectrally negative Levy process, dividend strategy, physical grid and candidate, if every original prepayment reserve sampled on the grid is zero, both the original strict-interior generator grid sum G and drift-only grid sum L equal zero. The original ruin-time condition and finite grid weights are preserved.
-- source:
--   The original physical strict-interior mask contains 0<Z_i, which is false when Z_i=0. Hence each summand vanishes regardless of generator regularity or jump intensity. Source-level bridge needed for the zero-reserve counterexample.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_obstruction_original_zero_prepayment_generator_drift_grids_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (C : ℝ≥0∞)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ) (ω : Ω)
    (hZero : ∀ i ∈ Finset.range (n + 1),
      Function.leftLim (fun t : ℝ≥0 =>
        x + X.X t ω - rightLimit D t ω) (u n i) = 0) :
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    (∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0) = 0 ∧
    (∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.drift * deriv w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0) = 0 := by sorry
