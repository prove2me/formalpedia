-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_quadratic_weighted_levy_measure_zero_atom
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_quadratic_weighted_levy_measure_zero_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:50:23.738788+00:00
-- url     : https://prove2.me/theorems/feeadba1-cf12-47a9-97b8-9bb92b695bbc
-- title:
--   Original squared-jump Levy weighted intensity has no zero atom
-- statement:
--   The genuine source Levy quadratic-weighted measure has no atom at zero, independently of the unweighted source atom.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_quadratic_weighted_levy_measure_zero_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    (X.ν.withDensity (fun z : ℝ => ENNReal.ofReal (z ^ 2)))
      ({0} : Set ℝ) = 0 := by sorry
