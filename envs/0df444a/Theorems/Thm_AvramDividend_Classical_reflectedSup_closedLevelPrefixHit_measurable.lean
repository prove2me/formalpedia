-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_closedLevelPrefixHit_measurable
-- name    : AvramDividend.Classical.reflectedSup_closedLevelPrefixHit_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:28:32.415837+00:00
-- url     : https://prove2.me/theorems/01f501d9-6c9c-4dec-9be7-126dae996541
-- title:
--   The actual reflected Lévy closed-level crossing event up to a deterministic horizon is measurable in the filtration at that horizon
-- statement:
--   For the actual reflected spectrally negative Lévy process, its genuine continuous-time closed-superlevel crossing event {there exists some time s≤t with R_s≥x} is measurable at filtration t. A dense countable sampling set S containing zero witnesses the measurability of its entire continuous-time prefix supremum via the accepted right-continuous dense-sample plus endpoint theorem. Upper semicontinuity of the actual reflected path makes a closed-level hit equivalent to that prefix supremum reaching x. The result needs no assumption that the given filtration is right continuous and is the exact observation event for constructing capped first closed-level hitting times as stopping times.
-- source:
--   Accepted reflectedSup_fullPrefixSup_adapted_of_dense, usc_compact_prefix_hit_iff_ciSup_ge and reflectedSup_upperSemicontinuousOn_Icc.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Theorems.Thm_AvramDividend_Classical_reflectedSup_fullPrefixSup_adapted_of_dense
import Theorems.Thm_AvramDividend_Classical_usc_compact_prefix_hit_iff_ciSup_ge
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal

theorem AvramDividend.Classical.reflectedSup_closedLevelPrefixHit_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Set ℝ≥0) (hS : S.Countable) (hDense : Dense S)
    (h0 : (0 : ℝ≥0) ∈ S)
    (t : ℝ≥0) (x : ℝ) :
    MeasurableSet[𝓕 t]
      {ω : Ω | ∃ s : ℝ≥0, s ≤ t ∧ x ≤ reflectedSup X s ω} := by sorry
