-- Prove2me | solution 1 for leftmostWitnessG_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:03:31.375057+00:00
-- url     : https://prove2.me/submissions/b7443abe-b4b2-4922-a264-a987af712fd0

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree

set_option autoImplicit false
open Set Topology MeasureTheory
open scoped Classical
noncomputable section
variable {X : Type*} [TopologicalSpace X]
omit [TopologicalSpace X]
theorem _root_.solution (F : Set (X × (ℕ → ℕ))) (x : X) (h₀ n) :
    leftmostWitnessG F x h₀ n ∈ closedFiberG F x :=
  ((leftmostAuxG F x h₀ n).2.some_mem).1
