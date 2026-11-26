-- Prove2me | solution 1 for eps_optimal_kernel_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T07:59:53.452636+00:00
-- url     : https://prove2.me/submissions/738990f9-a112-461e-be88-bafe0c72c63d

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_DescriptiveSetTheory_JankovVonNeumann
import Definitions.Def_BicausalOT_UpperBound
import Theorems.Thm_eps_optimal_selection


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
variable (c₀ : X₀ × Y₀ → ENNReal) (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)
theorem _root_.solution
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (h_ne : ∀ z₀ : X₀ × Y₀, (FeasibleSet₀ κ_μ κ_ν z₀).Nonempty)
    (ε : ENNReal) (hε : 0 < ε) :
    ∃ (γ₁ : X₀ × Y₀ → Measure (X₁ × Y₁)),
      (∀ z₀, γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀) ∧
      ∀ z₀, ∫⁻ z₁, c₁ (z₀, z₁) ∂(γ₁ z₀)
        ≤ (⨅ (m : Measure (X₁ × Y₁)) (_ : m ∈ FeasibleSet₀ κ_μ κ_ν z₀),
            ∫⁻ z₁, c₁ (z₀, z₁) ∂m) + ε := by
  obtain ⟨sel, h_feas, h_opt⟩ :=
    eps_optimal_selection (FeasibleSet₀ κ_μ κ_ν) h_ne
      (fun z₀ γ => ∫⁻ z₁, c₁ (z₀, z₁) ∂γ) ε hε
  exact ⟨sel, h_feas, h_opt⟩
