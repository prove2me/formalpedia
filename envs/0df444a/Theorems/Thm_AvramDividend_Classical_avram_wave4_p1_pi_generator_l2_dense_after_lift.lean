-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_pi_generator_l2_dense_after_lift
-- name    : AvramDividend.Classical.avram_wave4_p1_pi_generator_l2_dense_after_lift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:43:16.27674+00:00
-- url     : https://prove2.me/theorems/7a68dc8d-30f9-4c0e-8b9c-23fc9641088e
-- title:
--   Full finite-measure L² density of adapted marked Pi-system elementary generator indicators
-- statement:
--   Let μ be a finite measure and G a measurable Pi-system generating the exact ambient measurable space; derive the generated Boolean algebra's measure-density constructively via Mathlib's finite-measure monotone-class theorem. Prove that the bare indicators of G, after adjoining the universal and empty sets, have a dense finite REAL linear span in the full Hilbert space Lp ℝ 2 μ. First use the Proved Pi-system finite pointwise Boolean span and the independent genuine pointwise-to-L² lift to place every Boolean indicator L² class into the finite generator span. Then MeasureDense.indicatorConstLp_subset_closure and Lp.induction extend to every square integrable kernel. The proof justifies arbitrary predictable finite-rate marked-kernel approximation without assuming Campbell/isometry. Source 04-A must still establish the actual jump law.
-- source:
--   Requires canonically Proved Pi-system Boolean finite-span UUID c58acfdd and pending pointwise-to-L² Lp lifting target af412b58; pinned Mathlib MeasureDense.indicatorConstLp_subset_closure, Lp.induction, MemLp.toLp_const_smul.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_pi_system_boolean_indicator_span
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_pointwise_indicator_span_l2_lift

open MeasureTheory Set TopologicalSpace AvramDividend.Classical
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_wave4_p1_pi_generator_l2_dense_after_lift
    {α : Type*} [mα : MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (G : Set (Set α)) (hPi : IsPiSystem G)
    (hGm : ∀ t : Set α, t ∈ G → MeasurableSet t)
    (hGen : mα = MeasurableSpace.generateFrom G) :
    let GP : Set (Set α) :=
      insert Set.univ (insert (∅ : Set α) G)
    let S : Set (Lp ℝ (2 : ℝ≥0∞) μ) :=
      {v | ∃ (t : Set α) (ht : t ∈ GP)
        (htm : MeasurableSet t) (hμt : μ t ≠ ⊤),
        indicatorConstLp (2 : ℝ≥0∞) htm hμt (1 : ℝ) = v}
    ∀ f : Lp ℝ (2 : ℝ≥0∞) μ,
      f ∈ (Submodule.span ℝ S).topologicalClosure := by sorry
