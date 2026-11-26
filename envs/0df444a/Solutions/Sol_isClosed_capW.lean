-- Prove2me | solution 1 for isClosed_capW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:04:38.634935+00:00
-- url     : https://prove2.me/submissions/49564165-f0ed-44c5-a69c-304675e34c17

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Finiteness
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Theorems.Thm_capSeqs_finite

set_option autoImplicit false
open Set Topology MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section
variable {Z : Type*} [TopologicalSpace Z]
theorem _root_.solution (π : (ℕ → ℕ) → Z) (β : ℕ → ℕ) (n : ℕ) :
    IsClosed (capW π β n) :=
  (capSeqs_finite β n).isClosed_biUnion fun _ _ => isClosed_closure
