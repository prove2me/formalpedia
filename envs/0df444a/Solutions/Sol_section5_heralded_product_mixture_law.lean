-- Prove2me | solution 1 for section5_heralded_product_mixture_law
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:21:22.192319+00:00
-- url     : https://prove2.me/submissions/651d6da7-22cc-4c8d-96df-9abb1ac15b87

import Mathlib
import Theorems.Thm_section5_product_subsample_preserving
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal
theorem solution {T ι κ Ω : Type*}
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype ι] [Fintype κ]
    [MeasurableSpace Ω] (w : T → ℝ≥0∞) (hw : ∑ t,w t=1)
    (ν : T → ι → Measure Ω) [∀ t i, IsProbabilityMeasure (ν t i)]
    (μ : κ → Measure Ω) (e : T → κ ↪ ι) (hselected : ∀ t j, ν t (e t j)=μ j) :
    Measure.map (fun tx : T × (ι → Ω) => tx.2 ∘ e tx.1)
      (Measure.sum (fun t => w t • Measure.map (fun x : ι → Ω => (t,x)) (Measure.pi (ν t))))=
        Measure.pi μ := by
  have hmeas : Measurable (fun tx : T × (ι → Ω) => tx.2 ∘ e tx.1) :=
    measurable_from_prod_countable_right
      (fun t => measurable_pi_lambda _ (fun j => measurable_pi_apply (e t j)))
  have heach (t : T) : Measure.map (fun tx : T × (ι → Ω) => tx.2 ∘ e tx.1)
      (Measure.map (fun x : ι → Ω => (t,x)) (Measure.pi (ν t)))=Measure.pi μ := by
    have htag : Measurable (fun x : ι → Ω => (t,x)) := measurable_const.prodMk measurable_id
    rw [Measure.map_map hmeas htag]
    exact (section5_product_subsample_preserving (ν t) μ (e t) (hselected t)).map_eq
  rw [Measure.map_sum hmeas.aemeasurable]
  simp_rw [Measure.map_smul,heach]
  rw [Measure.sum_fintype,← Finset.sum_smul,hw,one_smul]
