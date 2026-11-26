-- Prove2me | solution 1 for exists_measurable_selection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:16:08.761796+00:00
-- url     : https://prove2.me/submissions/d27f5574-593d-47ec-aed5-c4761925f1e7

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Theorems.Thm_MeasurableSelection_exists_selection_of_denseRange

set_option autoImplicit false
open Metric Set Filter Topology TopologicalSpace
theorem _root_.solution {α : Type*} [MeasurableSpace α] {Y : Type*}
    [MetricSpace Y] [SeparableSpace Y] [CompleteSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] {Φ : α → Set Y} (hne : ∀ a, (Φ a).Nonempty)
    (hclosed : ∀ a, IsClosed (Φ a))
    (hmeas : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty}) :
    ∃ f : α → Y, Measurable f ∧ ∀ a, f a ∈ Φ a := by
  rcases isEmpty_or_nonempty α with hα | hα
  · haveI := hα
    exact ⟨fun a => (hne a).some, measurable_of_empty _, fun a => (hne a).some_mem⟩
  · obtain ⟨a₀⟩ := hα
    haveI : Nonempty Y := ⟨(hne a₀).some⟩
    obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq Y
    exact MeasurableSelection.exists_selection_of_denseRange hu hne hclosed hmeas
