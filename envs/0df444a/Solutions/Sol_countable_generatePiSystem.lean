-- Prove2me | solution 1 for countable_generatePiSystem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:06:51.359452+00:00
-- url     : https://prove2.me/submissions/31e247b7-df46-4097-b103-2c0b1bd1caf6

import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Measure.GiryMonad
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish

set_option autoImplicit false
open MeasureTheory Topology TopologicalSpace Metric Filter Set
open scoped ENNReal NNReal Classical
noncomputable section
theorem _root_.solution {α : Type*} {S : Set (Set α)}
    (hS : S.Countable) : (generatePiSystem S).Countable := by
  refine ((countable_ofPred_finite_subset hS).image fun T => ⋂₀ T).mono
    fun t ht => ?_
  induction ht with
  | base h_s =>
    exact ⟨{_}, ⟨finite_singleton _, singleton_subset_iff.mpr h_s⟩,
      sInter_singleton _⟩
  | inter _ _ _ ih_s ih_u =>
    obtain ⟨T₁, ⟨hT₁fin, hT₁sub⟩, rfl⟩ := ih_s
    obtain ⟨T₂, ⟨hT₂fin, hT₂sub⟩, rfl⟩ := ih_u
    exact ⟨T₁ ∪ T₂, ⟨hT₁fin.union hT₂fin, union_subset hT₁sub hT₂sub⟩,
      sInter_union T₁ T₂⟩
