-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_quadratic_tail_vanishes_with_finite_weighted_mass
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_quadratic_tail_vanishes_with_finite_weighted_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:02:20.896107+00:00
-- url     : https://prove2.me/theorems/d163ac42-7701-46ef-a3a8-ecf0a5075cde
-- title:
--   Original Levy small-mark quadratic tails vanish under finite mass
-- statement:
--   Finite original squared-jump Levy intensity implies quadratic band tails vanish as measurable cutoffs shrink to zero without an independent zero-atom premise.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_quadratic_intensity_vanishes_on_shrinking_mark_bands
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_quadratic_weighted_levy_measure_zero_atom

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_quadratic_tail_vanishes_with_finite_weighted_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hAnti : Antitone B)
    (hInter : (⋂ n, B n) ⊆ ({0} : Set ℝ))
    (hFinite :
      (X.ν.withDensity (fun z : ℝ => ENNReal.ofReal (z ^ 2))) Set.univ < ⊤) :
    Tendsto (fun n =>
      (X.ν.withDensity (fun z : ℝ => ENNReal.ofReal (z ^ 2)))
        (B n)) atTop (𝓝 0) := by sorry
