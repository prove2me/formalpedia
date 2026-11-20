-- Prove2me | solution 1 for measurable_limUnder
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T08:19:42.804049+00:00
-- url     : https://prove2.me/submissions/221eba50-afe5-4026-a611-3b146e80c612

import Definitions.Def_BrownianMotion_Continuity_LimitModification_F000

/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
#

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section aux

theorem _root_.solution {ι X E : Type*} [MeasurableSpace X] [TopologicalSpace E] [PolishSpace E]
    [MeasurableSpace E] [BorelSpace E] [Countable ι] {l : Filter ι}
    [l.IsCountablyGenerated] {f : ι → X → E} [hE : Nonempty E] (hf : ∀ i, Measurable (f i)) :
    Measurable (fun x ↦ limUnder l (f · x)) := by
  classical
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable E
  rcases l.eq_or_neBot with rfl | hl
  · simp only [limUnder, Filter.map_bot]
    exact measurable_const
  set S := {x | ∃ c, Tendsto (f · x) l (𝓝 c)} with hS_def
  have hS : MeasurableSet S := measurableSet_exists_tendsto hf
  have h_off : ∀ x ∉ S, limUnder l (f · x) = Classical.choice hE := by
    intro x hx
    have hne : ¬ ∃ a, Filter.map (f · x) l ≤ 𝓝 a := fun ⟨a, ha⟩ => hx ⟨a, ha⟩
    simp only [limUnder, lim, Classical.epsilon, Classical.strongIndefiniteDescription, dif_neg hne]
  refine measurable_of_restrict_of_restrict_compl hS ?_ ?_
  · refine measurable_of_tendsto_metrizable' l
      (f := fun i (x : S) => f i x) (fun i => (hf i).comp measurable_subtype_coe) ?_
    rw [tendsto_pi_nhds]
    intro x
    exact tendsto_nhds_limUnder x.2
  · have : (fun x : (Sᶜ : Set X) => limUnder l (f · (x : X))) = fun _ => Classical.choice hE :=
      funext fun x => h_off x x.2
    change Measurable (fun x : (Sᶜ : Set X) => limUnder l (f · (x : X)))
    rw [this]
    exact measurable_const

end aux
