-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_source_product_rectangle_mass_of_cutoffs
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_source_product_rectangle_mass_of_cutoffs
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:42:37.019395+00:00
-- url     : https://prove2.me/theorems/dfaa71a5-67ae-4576-b2b1-851205866ccd
-- title:
--   Original Lévy product compensator from off-zero cutoffs
-- statement:
--   Original-source Levy measure product intensity rectangle mass after discharging sigma finiteness from cutoff mass.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_source_levy_measure_sfinite_of_cutoffs
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_source_compensator_rectangle_mass_of_sfinite

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_source_product_rectangle_mass_of_cutoffs
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hZero : X.ν ({0} : Set ℝ) = 0)
    (hAway : ∀ n : ℕ,
      X.ν {z : ℝ | 1 / ((n : ℝ) + 1) ≤ |z|} < ⊤)
    (timeMeasure : Measure ℝ≥0) (s t : ℝ≥0) (B : Set ℝ)
    (hTimeVolume : timeMeasure (Ioc s t) =
      ((t - s : ℝ≥0) : ℝ≥0∞)) :
    (timeMeasure.prod X.ν) (Ioc s t ×ˢ B) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
