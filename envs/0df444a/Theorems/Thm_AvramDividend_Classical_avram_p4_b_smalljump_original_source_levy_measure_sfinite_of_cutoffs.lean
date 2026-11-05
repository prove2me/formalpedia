-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_source_levy_measure_sfinite_of_cutoffs
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_source_levy_measure_sfinite_of_cutoffs
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:23:32.616915+00:00
-- url     : https://prove2.me/theorems/1458b6bf-e57e-4c8d-8b51-336afc6893c6
-- title:
--   Original Lévy source measure is s-finite from off-zero intensity bounds
-- statement:
--   The genuine original Lévy measure X.ν is s-finite if its zero atom vanishes and every reciprocal-distance off-zero mark set has finite intensity.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_source_levy_measure_sfinite_of_cutoffs
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hZero : X.ν ({0} : Set ℝ) = 0)
    (hAway : ∀ n : ℕ,
      X.ν {z : ℝ | 1 / ((n : ℝ) + 1) ≤ |z|} < ⊤) :
    SFinite X.ν := by sorry
