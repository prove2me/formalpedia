-- Prove2me | solution 1 for leftmostWitnessG_agrees
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:03:39.656291+00:00
-- url     : https://prove2.me/submissions/9973805b-31a3-4ef1-8e7a-93c8a2dc61f3

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
import Theorems.Thm_leftmostAuxG_eq

set_option autoImplicit false
open Set Topology MeasureTheory
open scoped Classical
noncomputable section
variable {X : Type*} [TopologicalSpace X]
omit [TopologicalSpace X]
theorem _root_.solution (F : Set (X × (ℕ → ℕ))) (x : X) (h₀ n i) (hi : i < n) :
    leftmostWitnessG F x h₀ n i = leftmostBranchG F x h₀ i := by
  have := ((leftmostAuxG F x h₀ n).2.some_mem).2 i hi
  rw [leftmostAuxG_eq F x h₀ n i hi] at this; exact this
