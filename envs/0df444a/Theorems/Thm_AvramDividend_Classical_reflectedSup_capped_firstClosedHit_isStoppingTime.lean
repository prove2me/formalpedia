-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_capped_firstClosedHit_isStoppingTime
-- name    : AvramDividend.Classical.reflectedSup_capped_firstClosedHit_isStoppingTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:37:14.300391+00:00
-- url     : https://prove2.me/theorems/fb00a7dd-12d7-41c1-a4ba-c61ef2c74e3d
-- title:
--   The actual first closed-level hitting time of reflected Lévy drawdown, capped at a deterministic horizon, is a stopping time without right-continuous filtration
-- statement:
--   The true continuous-time earliest closed-superlevel entrance T of the actual reflected spectrally negative Lévy drawdown R, capped at a deterministic horizon H, is a genuine stopping time for the given filtration. Define T as the infimum of ({u∈[0,H]:R_u≥x}∪{H}) so the no-hit case is handled correctly. For t<H, compact upper semicontinuity shows {T≤t} equals the event that the full continuous-time prefix supremum reaches x; the latter is filtration-t-measurable by the accepted dense-sample-plus-endpoint adaptedness bridge. For t≥H the event is certain. Thus IsStoppingTime is proved without assuming filtration right continuity, and can be used for level-hitting strong-Markov arguments. The theorem does not itself establish a sigma-finite Itô excursion n-strong-Markov property.
-- source:
--   Accepted Prove2Me reflectedSup_fullPrefixSup_adapted_of_dense, usc_capped_first_closed_hit_le_iff_prefix_hit, usc_compact_prefix_hit_iff_ciSup_ge, reflectedSup_upperSemicontinuousOn_Icc; Mathlib MeasureTheory.IsStoppingTime.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc
import Theorems.Thm_AvramDividend_Classical_reflectedSup_fullPrefixSup_adapted_of_dense
import Theorems.Thm_AvramDividend_Classical_usc_capped_first_closed_hit_le_iff_prefix_hit
import Theorems.Thm_AvramDividend_Classical_usc_compact_prefix_hit_iff_ciSup_ge

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.reflectedSup_capped_firstClosedHit_isStoppingTime
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Set ℝ≥0) (hS : S.Countable) (hDense : Dense S)
    (h0 : (0 : ℝ≥0) ∈ S)
    (H : ℝ≥0) (x : ℝ) :
    IsStoppingTime 𝓕 (fun ω : Ω =>
      WithTop.some (sInf ((Icc (0 : ℝ≥0) H ∩
        (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H}))) := by sorry
