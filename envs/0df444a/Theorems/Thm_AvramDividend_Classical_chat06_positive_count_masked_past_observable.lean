-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_positive_count_masked_past_observable
-- name    : AvramDividend.Classical.chat06_positive_count_masked_past_observable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T15:52:52.045652+00:00
-- url     : https://prove2.me/theorems/16c87328-b687-444b-a6a0-4f5031925fa5
-- title:
--   Positive count event as an almost-sure measurable-past cylinder
-- statement:
--   A positive count event that agrees almost surely with consecutive arrival inequalities is measurable from the zero-padded finite waiting prefix.
-- source:
--   Verified source complete private candidate at pinned Mathlib revision; source and remote job recorded in Chat 06 SUBMISSIONS.json. Preamble defines the local arrival/prefix functions used by exact statement.

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Topology.Order.Basic

open MeasureTheory Set
namespace AvramChat06

/-- A fixed-codomain, sequence-valued observation of only the
first k exponential waiting times. Later coordinates are zero. -/
def maskedWaitPrefix {Ω : Type*}
    (τ : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) (i : ℕ) : ℝ :=
  if i < k then τ i ω else 0

/-- Cylinder for the event that observation time t is between
the (n+1)-st and (n+2)-nd arrival times. -/
def positiveCountPastCylinder (n : ℕ) (t : ℝ) :
    Set (ℕ → ℝ) :=
  {g | (∑ i ∈ Finset.range (n + 1), g i) ≤ t ∧
    t < ∑ i ∈ Finset.range (n + 2), g i}

end AvramChat06
open AvramChat06

theorem AvramDividend.Classical.chat06_positive_count_masked_past_observable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (τ : ℕ → Ω → ℝ) (N : Ω → ℕ) (n : ℕ) (t : ℝ)
    (hAE : (fun ω : Ω => N ω = n + 1) =ᵐ[P]
      (fun ω : Ω =>
        (∑ i ∈ Finset.range (n + 1), τ i ω) ≤ t ∧
        t < ∑ i ∈ Finset.range (n + 2), τ i ω)) :
    ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = n + 1) =ᵐ[P]
        (fun ω : Ω => maskedWaitPrefix τ (n + 2) ω ∈ S) := by sorry
