-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f14_original_near_zero_rational_germ_measurable
-- name    : AvramDividend.Classical.avram_p4_f14_original_near_zero_rational_germ_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T19:34:53.237362+00:00
-- url     : https://prove2.me/theorems/591f0950-bcb5-4926-aa17-d6fb7f87c76f
-- title:
--   Countable rational-time positive excursion event lies in the original Lévy germ
-- statement:
--   Represent the rational-time arbitrarily-early positive excursion event as a countable intersection over shrinking positive horizons of countable unions of positive coordinate inequalities. Every sufficiently small term is measurable in each finite-time past sigma field; hence the event belongs to the time-zero germ.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_DurrettProbability_Brownian
open MeasureTheory Set AvramDividend.Classical DurrettProbability
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f14_original_near_zero_rational_germ_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    MeasurableSet[germSigma X.X] {ω : Ω | ∀ ε : ℝ≥0, 0 < ε →
      ∃ q : ℚ≥0, (q : ℝ≥0) < ε ∧ 0 < X.X (q : ℝ≥0) ω} := by sorry
