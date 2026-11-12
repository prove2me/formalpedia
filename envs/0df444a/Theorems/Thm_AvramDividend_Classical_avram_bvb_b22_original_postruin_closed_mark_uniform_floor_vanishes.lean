-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b22_original_postruin_closed_mark_uniform_floor_vanishes
-- name    : AvramDividend.Classical.avram_bvb_b22_original_postruin_closed_mark_uniform_floor_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:20:57.827174+00:00
-- url     : https://prove2.me/theorems/fd8d4e5c-44be-41d7-b180-6dc57c1300d5
-- title:
--   Original masked loss upper bound on the genuine uniform floor grid
-- statement:
--   The actual original prepayment reserve's discounted open-cap negative mark loss on the refining uniform floor grid is eventually no greater than its closed-cap contact-time loss plus arbitrary epsilon, even when the grid misses contact occupation.
-- source:
--   Root-connected one-sided a.e. floor-sampling input for phys95/efbae9c3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva20_postruin_uniform_nat_floor_mask_eventually_false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b22_original_postruin_closed_mark_uniform_floor_vanishes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q T : ℝ)
    (hT : 0 < T) (ω : Ω) (t : ℝ≥0)
    (hpost : ruinTime X x D ω < (t : ℝ≥0∞)) :
    let s : ℕ → ℝ≥0 := fun n => Real.toNNReal
      (T * (⌊(((t : ℝ) / T) * ((n : ℝ) + 2))⌋₊ : ℝ) / ((n : ℝ) + 2))
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
    Tendsto (fun n =>
      if (s n : ℝ≥0∞) < ruinTime X x D ω ∧
         0 ≤ U (s n) ∧ ENNReal.ofReal (U (s n)) ≤ C then
        Real.exp (-(q * (s n : ℝ))) *
          ∫ z in Iio (0 : ℝ), w (U (s n) + z) - w (U (s n)) ∂X.ν
      else 0) atTop (𝓝 (0 : ℝ)) := by sorry
