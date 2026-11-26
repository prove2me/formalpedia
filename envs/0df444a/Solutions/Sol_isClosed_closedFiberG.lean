-- Prove2me | solution 1 for isClosed_closedFiberG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:03:30.781044+00:00
-- url     : https://prove2.me/submissions/7056c8a8-7c9b-4c08-8fc9-641ace0325dd

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
theorem _root_.solution {F : Set (X × (ℕ → ℕ))} (hF : IsClosed F) (x : X) :
    IsClosed (closedFiberG F x) :=
  hF.preimage (Continuous.prodMk continuous_const continuous_id)
