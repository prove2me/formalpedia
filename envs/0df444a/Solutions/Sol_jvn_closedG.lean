-- Prove2me | solution 1 for jvn_closedG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:06:50.919015+00:00
-- url     : https://prove2.me/submissions/2c45a660-c1cc-4e2d-8ae6-6ab3fde1fc70

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
import Theorems.Thm_closedUniformizerG_selection
import Theorems.Thm_closedUniformizerG_analyticallyMeasurable

set_option autoImplicit false
open Set Topology MeasureTheory
open scoped Classical
noncomputable section
variable {X : Type*} [TopologicalSpace X]
theorem _root_.solution [PolishSpace X]
    {F : Set (X × (ℕ → ℕ))} (hF : IsClosed F) (hne : F.Nonempty) :
    ∃ (φ : X → (ℕ → ℕ)), AnalyticallyMeasurable φ ∧
      ∀ x ∈ Prod.fst '' F, (x, φ x) ∈ F :=
  ⟨closedUniformizerG F hF hne,
   closedUniformizerG_analyticallyMeasurable hF hne,
   fun _ hx => closedUniformizerG_selection hF hne hx⟩
