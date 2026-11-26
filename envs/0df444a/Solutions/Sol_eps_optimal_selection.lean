-- Prove2me | solution 1 for eps_optimal_selection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T07:59:16.349997+00:00
-- url     : https://prove2.me/submissions/ce9053f7-5508-4858-82fa-84060afdaaed

import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_BicausalOT_DescriptiveSetTheory_JankovVonNeumann
section
open MeasureTheory Set ENNReal
noncomputable section
private theorem eps_optimal_element'
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
end
end

set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
theorem _root_.solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (S : α → Set (Measure β))
    (h_ne : ∀ a, (S a).Nonempty)
    (f : α → Measure β → ENNReal)
    (ε : ENNReal) (hε : 0 < ε) :
    ∃ (sel : α → Measure β),
      (∀ a, sel a ∈ S a) ∧
      (∀ a, f a (sel a) ≤ (⨅ (m : Measure β) (_ : m ∈ S a), f a m) + ε) := by
  have key : ∀ a, ∃ m ∈ S a, f a m ≤ (⨅ (m : Measure β) (_ : m ∈ S a), f a m) + ε :=
    fun a => eps_optimal_element' (S a) (h_ne a) (f a) ε hε
  choose sel hsel_mem hsel_opt using key
  exact ⟨sel, hsel_mem, hsel_opt⟩
