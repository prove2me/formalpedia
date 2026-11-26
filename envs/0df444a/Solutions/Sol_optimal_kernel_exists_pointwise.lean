-- Prove2me | solution 1 for optimal_kernel_exists_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T07:59:54.645677+00:00
-- url     : https://prove2.me/submissions/c281bae6-4a72-402c-8df7-d49131c3c3d6

import Definitions.Def_BicausalOT_Defs
import Mathlib.Topology.Semicontinuity.Basic
import Definitions.Def_BicausalOT_Existence

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
variable (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)
set_option linter.unusedSectionVars false
theorem _root_.solution
    [TopologicalSpace (Measure (X₁ × Y₁))]
    (κ_μ : X₀ → Measure X₁) (κ_ν : Y₀ → Measure Y₁)
    (z₀ : X₀ × Y₀)
    (h_ne : (FeasibleSet₀ κ_μ κ_ν z₀).Nonempty)
    (h_compact : IsCompact (FeasibleSet₀ κ_μ κ_ν z₀ :
        Set (Measure (X₁ × Y₁))))
    (h_lsc : LowerSemicontinuousOn
        (fun γ : Measure (X₁ × Y₁) => ∫⁻ z₁, c₁ (z₀, z₁) ∂γ)
        (FeasibleSet₀ κ_μ κ_ν z₀)) :
    ∃ γ_star ∈ FeasibleSet₀ κ_μ κ_ν z₀,
      ∀ γ ∈ FeasibleSet₀ κ_μ κ_ν z₀,
        ∫⁻ z₁, c₁ (z₀, z₁) ∂γ_star ≤ ∫⁻ z₁, c₁ (z₀, z₁) ∂γ := by
  obtain ⟨a, ha_mem, ha_min⟩ := h_lsc.exists_isMinOn h_ne h_compact
  exact ⟨a, ha_mem, fun γ hγ => ha_min hγ⟩
