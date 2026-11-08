-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_raw_R_nonnegative_bounded_clock
-- name    : AvramDividend.Classical.avram_bv_residual9_original_raw_R_nonnegative_bounded_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:09:43.054798+00:00
-- url     : https://prove2.me/theorems/0671ce2e-b384-4f9f-9169-308dd928d0d6
-- title:
--   Original bounded-variation raw remainder starts at zero and stays between zero and its finite-horizon endpoint
-- statement:
--   On the same full event as the Proved original BV raw-R monotonicity theorem, the actual raw J/R Stieltjes remainder is zero at time zero and lies between zero and R(T) throughout every fixed finite horizon. This supplies the endpoint positivity and domination needed for integrability of bounded random-weighted raw-J/R mesh corrections, without claiming R vanishes.
-- source:
--   AVRAM BV-RESIDUAL9 original raw R compact-clock localisation

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_original_raw_R_nonnegative_bounded_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      R 0 = 0 ∧ ∀ t : ℝ≥0, t ≤ T → 0 ≤ R t ∧ R t ≤ R T := by sorry
