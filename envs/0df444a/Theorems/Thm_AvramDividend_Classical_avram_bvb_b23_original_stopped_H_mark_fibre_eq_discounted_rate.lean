-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b23_original_stopped_H_mark_fibre_eq_discounted_rate
-- name    : AvramDividend.Classical.avram_bvb_b23_original_stopped_H_mark_fibre_eq_discounted_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:01:10.431573+00:00
-- url     : https://prove2.me/theorems/9d050946-aaf1-4ecc-9013-90e0fe66ff5e
-- title:
--   Original masked loss upper bound on the genuine uniform floor grid
-- statement:
--   The actual original prepayment reserve's discounted open-cap negative mark loss on the refining uniform floor grid is eventually no greater than its closed-cap contact-time loss plus arbitrary epsilon, even when the grid misses contact occupation.
-- source:
--   Root-connected one-sided a.e. floor-sampling input for phys95/efbae9c3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b23_original_stopped_H_mark_fibre_eq_discounted_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q T : ℝ)
    (n : ℕ) (ω : Ω) (t : ℝ≥0) :
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
    let good : Prop := 0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
      (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
      0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
    (∫ z, (if good ∧ z < 0 then Real.exp (-(q * (t : ℝ))) *
      (w (U t + z) - w (U t)) else 0)
      ∂(X.ν.restrict (Iio (0 : ℝ)))) =
    if good then Real.exp (-(q * (t : ℝ))) *
      (∫ z in Iio (0 : ℝ), w (U t + z) - w (U t) ∂X.ν)
    else 0 := by sorry
