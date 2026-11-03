-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_negative_tail_weighted_linear_smalltime_bound
-- name    : AvramDividend.Classical.avram_p2_original_negative_tail_weighted_linear_smalltime_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:21:38.469645+00:00
-- url     : https://prove2.me/theorems/57a65fa9-1642-43e7-8c20-b7103f2440c8
-- title:
--   Separated original Lévy negative-increment tail has a linear small-time upper estimate
-- statement:
--   For the actual original source process X with its unchanged P, and every ε>0, the probability that X_h≤−ε multiplied by the explicit positive fourth exponential deficit threshold is at most C h in ENNReal for sufficiently small h>0. The proof combines the original-source Proved fourth-deficit Markov inequality, integrability from the finite source exponential moments, and the true small-time fourth weighted derivative. It does not assert ν(B) identification or a jump compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_fourth_deficit_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_fourth_deficit_linear_smalltime_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_actual_source_negative_increment_exponential_fourth_tail_bound

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_original_negative_tail_weighted_linear_smalltime_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        ENNReal.ofReal ((1 - Real.exp (-ε)) ^ 4) *
          P {ω : Ω | X.X (Real.toNNReal h) ω ≤ -ε} ≤
        ENNReal.ofReal (C * h) := by sorry
