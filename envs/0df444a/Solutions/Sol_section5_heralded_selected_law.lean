-- Prove2me | solution 1 for section5_heralded_selected_law
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:19:55.179268+00:00
-- url     : https://prove2.me/submissions/0740d798-a28a-4f66-9cd2-ede349b67062

import Mathlib
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! Nonadaptive measurements can be made before selecting the nonblank particles:
injective subsampling of an IID experiment preserves its complete joint law. -/

theorem section5_iid_subsample_preserving {ι κ Ω : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (e : κ ↪ ι) :
    MeasurePreserving (fun x : ι → Ω => x ∘ e) (Measure.pi (fun _ : ι => μ))
      (Measure.pi (fun _ : κ => μ)) := by
  have hi := iIndepFun_pi (μ:=fun _ : ι => μ) (X:=fun _ => id) (fun _ => aemeasurable_id)
  have hs := hi.precomp e.injective
  have hm := hs.map_fun_eq_pi_map (fun i => (measurable_pi_apply (e i)).aemeasurable)
  simp_rw [(measurePreserving_eval (fun _ : ι => μ) _).map_eq] at hm
  exact ⟨measurable_pi_lambda _ (fun i => measurable_pi_apply (e i)),hm⟩



theorem section5_heralded_iid_subsample_preserving {T ι κ Ω : Type*}
    [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype ι] [Fintype κ]
    [MeasurableSpace Ω] (ν : Measure T) [IsProbabilityMeasure ν]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (e : T → κ ↪ ι) :
    MeasurePreserving (fun tx : T × (ι → Ω) => (tx.1,tx.2 ∘ e tx.1))
      (ν.prod (Measure.pi (fun _ : ι => μ))) (ν.prod (Measure.pi (fun _ : κ => μ))) := by
  apply (MeasurePreserving.id ν).skew_product (g:=fun t (x : ι → Ω) => x ∘ e t)
  · exact measurable_from_prod_countable_right
      (fun t => (section5_iid_subsample_preserving μ (e t)).measurable)
  · exact Filter.Eventually.of_forall (fun t => (section5_iid_subsample_preserving μ (e t)).map_eq)





end
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal
theorem solution {T ι κ Ω : Type*}
    [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype ι] [Fintype κ]
    [MeasurableSpace Ω] (ν : Measure T) [IsProbabilityMeasure ν]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (e : T → κ ↪ ι) :
    MeasurePreserving (fun tx : T × (ι → Ω) => tx.2 ∘ e tx.1)
      (ν.prod (Measure.pi (fun _ : ι => μ))) (Measure.pi (fun _ : κ => μ)) := by
  exact (measurePreserving_snd (μ:=ν) (ν:=Measure.pi (fun _ : κ => μ))).comp
    (section5_heralded_iid_subsample_preserving ν μ e)
