-- Prove2me | solution 1 for section5_product_subsample_preserving
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:20:09.647863+00:00
-- url     : https://prove2.me/submissions/4982c713-1426-4c25-88d2-2ac0f03e7646

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal
theorem solution {ι κ Ω : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace Ω] (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (μ : κ → Measure Ω) (e : κ ↪ ι) (hμ : ∀ i, ν (e i)=μ i) :
    MeasurePreserving (fun x : ι → Ω => x ∘ e) (Measure.pi ν) (Measure.pi μ) := by
  have hi := iIndepFun_pi (μ:=ν) (X:=fun _ => id) (fun _ => aemeasurable_id)
  have hs := hi.precomp e.injective
  have hm := hs.map_fun_eq_pi_map (fun i => (measurable_pi_apply (e i)).aemeasurable)
  simp_rw [(measurePreserving_eval ν _).map_eq,hμ] at hm
  exact ⟨measurable_pi_lambda _ (fun i => measurable_pi_apply (e i)),hm⟩
