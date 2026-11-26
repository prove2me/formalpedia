-- Prove2me | solution 1 for leftmostBranchG_least
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:03:44.883745+00:00
-- url     : https://prove2.me/submissions/c2ee9281-e65b-44bb-8d27-8748e0b5bbc3

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
theorem _root_.solution (F : Set (X × (ℕ → ℕ))) (x : X)
    (h₀ : (closedFiberG F x).Nonempty) (n k : ℕ)
    (hk : k < leftmostBranchG F x h₀ n) :
    ¬(fiberRestNG F x (Function.update (leftmostAuxG F x h₀ n).val n k) (n + 1)).Nonempty :=
  Nat.find_min (exists_extNG (leftmostAuxG F x h₀ n).2) hk
