-- Prove2me | solution 1 for kernel_decomp_implies_bicausal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T07:59:17.054603+00:00
-- url     : https://prove2.me/submissions/13894492-3f6b-4139-b75d-3f3d73ac6ebc

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_Proposition1

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
theorem _root_.solution
    (μ₀ : Measure X₀) (ν₀ : Measure Y₀)
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (π : Measure ((X₀ × X₁) × (Y₀ × Y₁)))
    (kd : KernelDecomp π)
    (h_coupling : kd.γ₀ ∈ CouplingSet₀ μ₀ ν₀)
    (h_feas : ∀ᵐ z₀ ∂kd.γ₀, kd.γ₁ z₀ ∈ FeasibleSet₀ κ_μ κ_ν z₀) :
    IsBicausal₂ μ₀ ν₀ κ_μ κ_ν π :=
  ⟨kd, h_coupling, h_feas⟩
