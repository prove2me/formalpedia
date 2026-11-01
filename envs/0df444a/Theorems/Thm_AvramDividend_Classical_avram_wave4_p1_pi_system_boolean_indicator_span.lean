-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_pi_system_boolean_indicator_span
-- name    : AvramDividend.Classical.avram_wave4_p1_pi_system_boolean_indicator_span
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:10:54.873331+00:00
-- url     : https://prove2.me/theorems/c58acfdd-c5a2-46f1-9628-2cfcb6b690b5
-- title:
--   Finite Boolean Pi-system indicators lie in span of bare Pi generators plus constant
-- statement:
--   For every Pi-system G of sets on any type, the indicator of any finite Boolean combination of G is a finite real linear combination of indicators of members of G, the empty set and full universe. Prove intersection stability of the enlarged G by IsPiSystem.insert_empty.insert_univ, use nonempty intersection closure or empty intersection, monotonicity of generateSetAlgebra, and the separately Proved generic intersection-closed finite-span result. This is the missing finite-rank algebraic reduction from marked predictable Boolean approximations to elementary adapted marked time-ray tensors, not a stochastic compensation assumption.
-- source:
--   Dependent on P1 generic Boolean indicator finite-span theorem target 2a12efad-bd64-49ac-8657-dea3c5f04da8 being Proved. Pinned Mathlib IsPiSystem.insert_empty / insert_univ and generateSetAlgebra_mono.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_boolean_indicator_span_of_inter_closed

open MeasureTheory Set AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_p1_pi_system_boolean_indicator_span
    {α : Type*} (G : Set (Set α))
    (hPi : IsPiSystem G)
    (s : Set α) (hs : s ∈ generateSetAlgebra G) :
    let GP : Set (Set α) :=
      insert Set.univ (insert (∅ : Set α) G)
    let χ : Set α → (α → ℝ) :=
      fun t => Set.indicator t (fun _ => (1 : ℝ))
    χ s ∈ Submodule.span ℝ
      {v : α → ℝ | ∃ (t : Set α), t ∈ GP ∧ χ t = v} := by sorry
