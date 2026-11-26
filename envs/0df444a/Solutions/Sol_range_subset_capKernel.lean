-- Prove2me | solution 1 for range_subset_capKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:04:17.275207+00:00
-- url     : https://prove2.me/submissions/c87ae929-775d-4b0b-aa29-a4297e9bf186

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Finiteness
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability

set_option autoImplicit false
open Set Topology MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section
variable {Z : Type*} [TopologicalSpace Z]
theorem _root_.solution (π : (ℕ → ℕ) → Z) : range π ⊆ capKernel π := by
  rintro _ ⟨σ, rfl⟩
  exact mem_iUnion.mpr ⟨σ, mem_iInter.mpr fun n =>
    subset_closure ⟨σ, fun i _ => rfl, rfl⟩⟩
