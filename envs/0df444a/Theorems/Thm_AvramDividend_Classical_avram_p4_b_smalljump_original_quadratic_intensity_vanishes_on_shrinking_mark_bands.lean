-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_quadratic_intensity_vanishes_on_shrinking_mark_bands
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_quadratic_intensity_vanishes_on_shrinking_mark_bands
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:46:33.043786+00:00
-- url     : https://prove2.me/theorems/dc423c4a-c643-4882-ba19-0f5dbb888ad6
-- title:
--   Original quadratic Levy intensity vanishes at small cutoffs
-- statement:
--   For the actual original source Levy measure, finite weighted quadratic intensity gives a vanishing mass on shrinking measurable mark sets with intersection at zero.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_quadratic_intensity_vanishes_on_shrinking_mark_bands
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hAnti : Antitone B)
    (hInter : (⋂ n, B n) ⊆ ({0} : Set ℝ))
    (hFinite :
      (X.ν.withDensity (fun z : ℝ => ENNReal.ofReal (z ^ 2))) Set.univ < ⊤)
    (hZero :
      (X.ν.withDensity (fun z : ℝ => ENNReal.ofReal (z ^ 2)))
        ({0} : Set ℝ) = 0) :
    Tendsto (fun n =>
      (X.ν.withDensity (fun z : ℝ => ENNReal.ofReal (z ^ 2)))
        (B n)) atTop (𝓝 0) := by sorry
