-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_boolean_indicator_span_of_inter_closed
-- name    : AvramDividend.Classical.avram_wave4_p1_boolean_indicator_span_of_inter_closed
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T18:41:03.523993+00:00
-- url     : https://prove2.me/theorems/2a12efad-bd64-49ac-8657-dea3c5f04da8
-- title:
--   Finite Boolean generator indicators lie in the finite real span of Pi-system indicators
-- statement:
--   Generic finite-dimensional algebraic predictable-tensor bridge: if a family of sets contains the universe and is closed under intersections, the pointwise real indicator of EVERY set in its finite Boolean algebra is a finite real linear combination of indicators of the original generating sets. Prove closure of the generator span under pointwise multiplication using two nested Submodule.span_induction arguments, since generator products are indicators of intersections. Indicators of complements are 1 minus the indicator and unions are indicator(s)+indicator(t)-indicator(s∩t); use the pinned generateSetAlgebra_induction. This solves the previously open Boolean-indicator-to-elementary-generator finite-span step and will apply to the original-filtration marked adapted Pi-system after adjoining the universe. Does not assume compensation or martingale/isometry conclusions.
-- source:
--   Pinned Mathlib SetAlgebra.generateSetAlgebra_induction and Submodule.span_induction; elementary function indicator identities established by pointwise membership case analysis. Independent of source-X ownership and other P1 theorems.

import Mathlib

open MeasureTheory Set

theorem AvramDividend.Classical.avram_wave4_p1_boolean_indicator_span_of_inter_closed
    {α : Type*} (G : Set (Set α))
    (hInter : ∀ (s : Set α), s ∈ G → ∀ (t : Set α), t ∈ G → s ∩ t ∈ G)
    (hUniv : (Set.univ : Set α) ∈ G)
    (s : Set α) (hs : s ∈ generateSetAlgebra G) :
    let χ : Set α → (α → ℝ) :=
      fun t => Set.indicator t (fun _ => (1 : ℝ))
    χ s ∈ Submodule.span ℝ
      {v : α → ℝ | ∃ (t : Set α), t ∈ G ∧ χ t = v} := by sorry
