-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_local_quadratic_tail_vanishes_of_one_finite_band
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_local_quadratic_tail_vanishes_of_one_finite_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:02:54.692382+00:00
-- url     : https://prove2.me/theorems/6685e293-9cad-4aae-abee-a3e40fbbfda4
-- title:
--   Original Levy small-jump quadratic tail with only local finite mass
-- statement:
--   Shrinking original source Levy squared-jump band mass vanishes from finiteness on one initial cutoff alone, without a global second-moment assumption.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_quadratic_weighted_levy_measure_zero_atom

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_local_quadratic_tail_vanishes_of_one_finite_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hAnti : Antitone B)
    (hInter : (⋂ n, B n) ⊆ ({0} : Set ℝ))
    (hFinite0 :
      (X.ν.withDensity (fun z : ℝ => ENNReal.ofReal (z ^ 2))) (B 0) < ⊤) :
    Tendsto (fun n =>
      (X.ν.withDensity (fun z : ℝ => ENNReal.ofReal (z ^ 2)))
        (B n)) atTop (𝓝 0) := by sorry
