-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_capped_closedLevelHit_stoppingTime
-- name    : AvramDividend.Classical.reflectedSup_capped_closedLevelHit_stoppingTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T22:52:29.4094+00:00
-- url     : https://prove2.me/theorems/65e9e67f-8f94-4914-9817-d67cf2d686b9
-- title:
--   The actual capped continuous-time first closed-level hit of reflected Lévy drawdown is a stopping time with no additional assumptions
-- statement:
--   For the canonical adapted spectrally negative Lévy process X and its actual reflected drawdown, define the finite-horizon closed-level first hitting time by inf{u∈[0,H]:R_u≥x}, using the deterministic fallback H when the level is not reached. This is a genuine stopping time under the filtration appearing in SpectrallyNegativeLevy, without assuming right-continuous filtration, choosing a dense observation grid externally, or requiring the level is ever hit. Existence of a countable dense time set containing zero is proved separately, so instantiate the accepted reflectedSup_capped_firstClosedHit_isStoppingTime with that witness. This is the clean interface for finite-horizon stochastic stopping arguments in the excursion-height atomlessness branch. It does not establish the sigma-finite excursion measure's own strong Markov property.
-- source:
--   Accepted Prove2Me reflectedSup_capped_firstClosedHit_isStoppingTime and exists_countable_dense_nnreal_time_set_zero.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_exists_countable_dense_nnreal_time_set_zero
import Theorems.Thm_AvramDividend_Classical_reflectedSup_capped_firstClosedHit_isStoppingTime

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.reflectedSup_capped_closedLevelHit_stoppingTime
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0) (x : ℝ) :
    IsStoppingTime 𝓕 (fun ω : Ω =>
      WithTop.some (sInf ((Icc (0 : ℝ≥0) H ∩
        (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H}))) := by sorry
