-- Prove2me | solution 1 for isClosed_couplings_hit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:16:36.842931+00:00
-- url     : https://prove2.me/submissions/e619bdd5-b9d1-4cf5-a31e-fd2d4596ef6e

import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Theorems.Thm_exists_tendsto_subseq_couplings

set_option autoImplicit false
open MeasureTheory Set Filter Topology
noncomputable section
variable {A B : Type*}
  [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [PolishSpace B] [MeasurableSpace B] [BorelSpace B]
theorem _root_.solution
    {C : Set (ProbabilityMeasure (A × B))} (hC : IsClosed C) :
    IsClosed {p : ProbabilityMeasure A × ProbabilityMeasure B |
      ∃ γ ∈ C, (γ : Measure (A × B)).map Prod.fst = (p.1 : Measure A) ∧
        (γ : Measure (A × B)).map Prod.snd = (p.2 : Measure B)} := by
  refine isClosed_of_closure_subset fun p hp => ?_
  rw [mem_closure_iff_seq_limit] at hp
  obtain ⟨ps, hmem, hlim⟩ := hp
  choose γs hγC hγfst hγsnd using hmem
  have hμ : Tendsto (fun n => (ps n).1) atTop (𝓝 p.1) :=
    ((continuous_fst.tendsto p).comp hlim)
  have hν : Tendsto (fun n => (ps n).2) atTop (𝓝 p.2) :=
    ((continuous_snd.tendsto p).comp hlim)
  obtain ⟨γ, hf, hs, φ, -, hφt⟩ :=
    exists_tendsto_subseq_couplings hμ hν hγfst hγsnd
  exact ⟨γ, hC.mem_of_tendsto hφt (Eventually.of_forall fun k => hγC (φ k)),
    hf, hs⟩
