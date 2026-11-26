-- Prove2me | solution 1 for eps_optimal_element
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T07:59:47.004056+00:00
-- url     : https://prove2.me/submissions/e3fd4bee-78fd-4deb-b8ca-bf0589f18cd8

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_DescriptiveSetTheory_JankovVonNeumann
import Definitions.Def_BicausalOT_UpperBound

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set ENNReal
noncomputable section
variable {X₀ X₁ Y₀ Y₁ : Type*}
variable [MeasurableSpace X₀] [MeasurableSpace X₁]
variable [MeasurableSpace Y₀] [MeasurableSpace Y₁]
variable (c₀ : X₀ × Y₀ → ENNReal) (c₁ : (X₀ × Y₀) × (X₁ × Y₁) → ENNReal)
theorem _root_.solution
    {α : Type*} (S : Set α) (h_ne : S.Nonempty)
    (f : α → ENNReal) (ε : ENNReal) (hε : 0 < ε) :
    ∃ a ∈ S, f a ≤ (⨅ (x : α) (_ : x ∈ S), f x) + ε := by
  by_contra h
  simp only [not_exists, not_and, not_le] at h
  obtain ⟨a, ha⟩ := h_ne
  have hlt := h a ha
  have : (⨅ (x : α) (_ : x ∈ S), f x) + ε ≤ ⨅ (x : α) (_ : x ∈ S), f x :=
    le_iInf fun x => le_iInf fun hx => le_of_lt (h x hx)
  by_cases htop : (⨅ (x : α) (_ : x ∈ S), f x) = ⊤
  · simp [htop] at hlt
  · exact absurd this (not_le.mpr (ENNReal.lt_add_right htop hε.ne'))
