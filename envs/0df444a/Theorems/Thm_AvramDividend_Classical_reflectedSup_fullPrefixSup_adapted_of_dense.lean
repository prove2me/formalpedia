-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_fullPrefixSup_adapted_of_dense
-- name    : AvramDividend.Classical.reflectedSup_fullPrefixSup_adapted_of_dense
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:17:07.537279+00:00
-- url     : https://prove2.me/theorems/d01ad7b2-c050-4832-9950-309f11c4657d
-- title:
--   The actual reflected Lévy process full continuous-time prefix supremum is adapted via dense-grid plus endpoint representation
-- statement:
--   The complete continuous-time supremum of the actual reflected spectrally negative Lévy process over [0,t] is adapted to its filtration. Fix any dense countable time set S containing zero. The already accepted dense_timeSup_with_endpoint theorem identifies the full prefix supremum with the maximum of the sampled running supremum over S∩[0,t] and R_t, provided the path is right-continuous and bounded above. Actual reflected right continuity and upper semicontinuity on compact intervals supply these path hypotheses. The general countable-sample adaptedness theorem and actual reflected adaptedness make both terms measurable in filtration t. Consequently no filtration right-continuity is required for full-prefix supremum adaptedness. This is a crucial bridge from sampled observability to true continuous-time first closed-superlevel hitting events.
-- source:
--   Accepted AvramDividend.Classical.dense_timeSup_with_endpoint, reflectedSup_right_continuous, reflectedSup_upperSemicontinuousOn_Icc, reflectedSup_adapted, and countable_pastSup_adapted_of_adapted.

import Mathlib.Probability.Process.Adapted
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Theorems.Thm_AvramDividend_Classical_reflectedSup_adapted
import Theorems.Thm_AvramDividend_Classical_reflectedSup_right_continuous
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc
import Theorems.Thm_AvramDividend_Classical_dense_timeSup_with_endpoint
import Theorems.Thm_AvramDividend_Classical_countable_pastSup_adapted_of_adapted

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal

theorem AvramDividend.Classical.reflectedSup_fullPrefixSup_adapted_of_dense
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Set ℝ≥0) (hS : S.Countable) (hDense : Dense S)
    (h0 : (0 : ℝ≥0) ∈ S) :
    Adapted 𝓕 (fun t ω =>
      ⨆ s : Set.Icc (0 : ℝ≥0) t, reflectedSup X s.1 ω) := by sorry
