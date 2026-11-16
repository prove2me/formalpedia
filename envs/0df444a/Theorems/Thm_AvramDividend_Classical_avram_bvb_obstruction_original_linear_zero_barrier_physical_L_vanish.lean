-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_linear_zero_barrier_physical_L_vanish
-- name    : AvramDividend.Classical.avram_bvb_obstruction_original_linear_zero_barrier_physical_L_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:42:19.698146+00:00
-- url     : https://prove2.me/theorems/da057a52-1972-4f7a-bbb8-392e4dccba38
-- title:
--   Actual original physical BV drift-only grid L vanishes at every mesh on an exact linear zero-barrier source path
-- statement:
--   At every physical mesh row lying inside [0,1], the original positive-reserve masked drift-only physical grid L is exactly zero on a unit-drift zero-barrier no-jump path. This supplies the missing source-specific L_n=0 condition for the positive-cap cash/nonconvergence obstruction.
-- source:
--   Proved zero-prepayment original source on every grid site (including origin) and Proved original zero-prepayment generator/drift grid vanishing pair, preserving exact original BV L definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_original_linear_zero_barrier_physical_L_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hDrift : X.drift = 1)
    (hPath : ∀ t : ℝ≥0, t ≤ (1 : ℝ≥0) →
      X.X t ω = (t : ℝ) * X.drift)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hWithin : ∀ i ∈ Finset.range (n + 1), u n i ≤ 1)
    (w : ℝ → ℝ) (q : ℝ) (C : ℝ≥0∞) :
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => (0 : ℝ) + X.X t ω -
        rightLimit (barrierStrategy X 0 0) t ω) (u n i)
    (∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < ruinTime X 0 (barrierStrategy X 0 0) ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.drift * deriv w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0) = 0 := by sorry
