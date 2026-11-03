-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_two_separated_marked_increment_cells_probability_product
-- name    : AvramDividend.Classical.avram_wave6_01_original_past_two_separated_marked_increment_cells_probability_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:34:18.156047+00:00
-- url     : https://prove2.me/theorems/7c4e6d15-242a-46be-ba5a-1c805226c0f1
-- title:
--   Original Levy past event and two separated Borel marked increment cells have joint product probability
-- statement:
--   For the unchanged original spectrally negative Levy process X on Ω with probability P and filtration F, a past event A in F_s and arbitrary Borel marks B,C on two time-disjoint source increments have exactly product joint probability. This is the original-process pairwise marked-cell first-moment input for elementary finite-grid Bernoulli second-moment and uniform-integrability estimates in the intrinsic jump-measure compensation proof; it identifies no unproved Levy intensity.
-- source:
--   Avram Wave6 Chat01 original jump-measure compensation, mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43. Direct first-step/second-step application of canonically Proved chat04_past_event_next_levy_increment_measure_product to the original adapted filtration. Useful for independent source Bernoulli-grid UI, with no Poisson proxy or compensated count premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_past_event_next_levy_increment_measure_product

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_01_original_past_two_separated_marked_increment_cells_probability_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s a b c d : ℝ≥0) (hsa : s ≤ a) (hab : a ≤ b)
    (hbc : b ≤ c) (hcd : c ≤ d)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    P (A ∩ ({ω | X.X b ω - X.X a ω ∈ B} ∩
      {ω | X.X d ω - X.X c ω ∈ C})) =
    P A * P {ω | X.X b ω - X.X a ω ∈ B} *
      P {ω | X.X d ω - X.X c ω ∈ C} := by sorry
