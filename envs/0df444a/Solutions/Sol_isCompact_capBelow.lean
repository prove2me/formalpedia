-- Prove2me | solution 1 for isCompact_capBelow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:04:39.134579+00:00
-- url     : https://prove2.me/submissions/0de242f6-d1ec-47d1-ab77-9d668718a34f

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic.Finiteness
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Theorems.Thm_capBelow_eq_pi

set_option autoImplicit false
open Set Topology MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section
theorem _root_.solution (β : ℕ → ℕ) : IsCompact (capBelow β) := by
  rw [capBelow_eq_pi]
  exact isCompact_univ_pi fun i => (Set.finite_Iic (β i)).isCompact
