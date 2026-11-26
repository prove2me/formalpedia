-- Prove2me | solution 1 for leftmostBranchG_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:04:19.725545+00:00
-- url     : https://prove2.me/submissions/2cdb122a-e3b4-49cb-8bc1-7922c2014921

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
import Theorems.Thm_isClosed_closedFiberG
import Theorems.Thm_leftmostWitnessG_mem
import Theorems.Thm_leftmostWitnessG_agrees

set_option autoImplicit false
open Set Topology MeasureTheory
open scoped Classical
noncomputable section
variable {X : Type*} [TopologicalSpace X]
theorem _root_.solution
    {F : Set (X × (ℕ → ℕ))} (hF : IsClosed F) (x : X)
    (h₀ : (closedFiberG F x).Nonempty) :
    (x, leftmostBranchG F x h₀) ∈ F :=
  (isClosed_closedFiberG hF x).mem_of_tendsto
    (tendsto_pi_nhds.mpr fun i => by
      rw [congr_fun (nhds_discrete ℕ) _]
      exact Filter.tendsto_pure.mpr (Filter.eventually_atTop.mpr
        ⟨i + 1, fun n hn => leftmostWitnessG_agrees F x h₀ n i (by omega)⟩))
    (Filter.Eventually.of_forall (leftmostWitnessG_mem F x h₀))
