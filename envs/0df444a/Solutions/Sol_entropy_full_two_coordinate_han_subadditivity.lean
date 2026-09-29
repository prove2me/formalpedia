-- Prove2me | solution 1 for entropy_full_two_coordinate_han_subadditivity
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-24T15:53:02.981949+00:00
-- url     : https://prove2.me/submissions/861f8210-296d-42e8-8a56-1a914cd23de6

import Theorems.Thm_entropy_chain_rule_general_two_coordinate_han_subadditivity
import Theorems.Thm_entropy_convexity_refinement_marginal_le_integral_fiber
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real MeasureTheory

/-- **Full two-coordinate Han subadditivity of entropy (BLM Thm 4.10).**

`Ent_m(h) = (∫ h log h dm) − (∫ h dm)·log(∫ h dm)`, written inline.  For probability
measures `μ, ν` and a positive integrable `f : α × β → ℝ`,

  `Ent_{μ⊗ν}(f)  ≤  ∫_y Ent_μ(f(·,y)) dν  +  ∫_x Ent_ν(f(x,·)) dμ.`

Reduction onto the two Proved children: the exact entropy chain rule
`entropy_chain_rule_general_two_coordinate_han_subadditivity` (equality form) and the
convexity refinement `entropy_convexity_refinement_marginal_le_integral_fiber`
(`Ent_μ(g₁) ≤ ∫_y Ent_μ(f(·,y)) dν`).  `rw` the chain rule, then `gcongr` against the
refinement.  Ledoux 1997 / Bousquet 2002 §3. -/
theorem solution
    {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α × β → ℝ}
    (hf_pos : ∀ p, 0 < f p)
    (hf_int : Integrable f (μ.prod ν))
    (hflog_int : Integrable (fun p ↦ f p * Real.log (f p)) (μ.prod ν))
    (hg1log_int : Integrable (fun x ↦ (∫ y, f (x, y) ∂ν) * Real.log (∫ y, f (x, y) ∂ν)) μ)
    (hm_int : Integrable (fun y ↦ ∫ x, f (x, y) ∂μ) ν)
    (hfx_int : ∀ x, Integrable (fun y ↦ f (x, y)) ν)
    (hfx_logm_int : ∀ x, Integrable (fun y ↦ f (x, y) * Real.log (∫ x', f (x', y) ∂μ)) ν)
    (hfx_logf_int : ∀ x, Integrable (fun y ↦ f (x, y) * Real.log (f (x, y))) ν)
    (h_inner_x_int :
      Integrable (fun x ↦ ∫ y, (f (x, y) * Real.log (f (x, y))
        - f (x, y) * Real.log (∫ x', f (x', y) ∂μ)) ∂ν) μ)
    (hfm_prod_int :
      Integrable (fun p : α × β ↦ f p * Real.log (∫ x', f (x', p.2) ∂μ)) (μ.prod ν)) :
    ((∫ p, f p * Real.log (f p) ∂(μ.prod ν))
        - (∫ p, f p ∂(μ.prod ν)) * Real.log (∫ p, f p ∂(μ.prod ν)))
      ≤ (∫ y, ((∫ x, f (x, y) * Real.log (f (x, y)) ∂μ)
            - (∫ x, f (x, y) ∂μ) * Real.log (∫ x, f (x, y) ∂μ)) ∂ν)
        + ∫ x, ((∫ y, f (x, y) * Real.log (f (x, y)) ∂ν)
            - (∫ y, f (x, y) ∂ν) * Real.log (∫ y, f (x, y) ∂ν)) ∂μ := by
  rw [entropy_chain_rule_general_two_coordinate_han_subadditivity hf_int hflog_int hg1log_int]
  gcongr
  exact entropy_convexity_refinement_marginal_le_integral_fiber hf_pos hf_int hflog_int
    hg1log_int hm_int hfx_int hfx_logm_int hfx_logf_int h_inner_x_int hfm_prod_int

#print axioms solution
