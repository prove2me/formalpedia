-- Prove2me | Theorems.Thm_AvramDividend_Classical_monotone_usc_capped_superlevel_isStoppingTime
-- name    : AvramDividend.Classical.monotone_usc_capped_superlevel_isStoppingTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:38:59.966889+00:00
-- url     : https://prove2.me/theorems/903d051e-db8d-4038-a0d3-d3207060a36b
-- title:
--   The actual first closed-superlevel hit of any adapted increasing upper-semicontinuous process, capped at finite horizon, is a stopping time
-- statement:
--   For an adapted real-valued process u that is pointwise nondecreasing and upper semicontinuous on every finite nonnegative-time interval, the true continuous-time first entrance at or above any fixed level a, with deterministic fallback horizon H when no hit occurs, is a stopping time for the given filtration. At every t<H, the accepted compact upper-semicontinuous capped first-hit event equivalence and monotonicity make {τ≤t} exactly {a≤u_t}; adaptedness makes it filtration-t-measurable. At t≥H the event is certain. No filtration right-continuity assumption is needed. This generic theorem is the key stopping-time interface for the inverse local-time clock of the actual spectrally negative Lévy running-supremum regulator.
-- source:
--   Accepted usc_capped_first_closed_hit_le_iff_prefix_hit, pinned Mathlib IsStoppingTime and Adapted; runningSup regulator is actual local time candidate.

import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_AvramDividend_Classical_usc_capped_first_closed_hit_le_iff_prefix_hit

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.monotone_usc_capped_superlevel_isStoppingTime
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (u : ℝ≥0 → Ω → ℝ) (hu : Adapted 𝓕 u)
    (hmono : ∀ ω : Ω, Monotone (fun t => u t ω))
    (husc : ∀ (ω : Ω) (H : ℝ≥0),
      UpperSemicontinuousOn (fun t => u t ω) (Icc 0 H))
    (H : ℝ≥0) (a : ℝ) :
    IsStoppingTime 𝓕 (fun ω : Ω =>
      WithTop.some (sInf ((Icc (0 : ℝ≥0) H ∩
        (fun t : ℝ≥0 => u t ω) ⁻¹' Ici a) ∪ {H}))) := by sorry
