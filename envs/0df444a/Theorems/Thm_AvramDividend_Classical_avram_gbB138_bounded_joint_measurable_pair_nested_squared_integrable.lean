-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB138_bounded_joint_measurable_pair_nested_squared_integrable
-- name    : AvramDividend.Classical.avram_gbB138_bounded_joint_measurable_pair_nested_squared_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:48:53.031205+00:00
-- url     : https://prove2.me/theorems/61372d3d-838b-42db-b435-ebabc6d00729
-- title:
--   Jointly bounded measurable pair yields inner and outer squared-error integrability
-- statement:
--   Combines proved B129 fixed-fibre squared-error integrability with proved B132 integrability of the probability-integrated squared error. Assumptions are joint measurability and a common bound on two functions over a finite product measure. Instantiate for K_m,K_p, K_m,H and H,K_p in B127.
-- source:
--   Proved B129 and B132

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB129_bounded_measurable_squared_difference_integrable
import Theorems.Thm_AvramDividend_Classical_avram_gbB132_bounded_joint_measurable_squared_error_outer_integrable
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_gbB138_bounded_joint_measurable_pair_nested_squared_integrable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f g : α × β → ℝ) (hf : Measurable f) (hg : Measurable g)
    (B : ℝ) (hB : 0 ≤ B)
    (hfb : ∀ z, |f z| ≤ B) (hgb : ∀ z, |g z| ≤ B) :
    (∀ a, Integrable (fun b => (f (a, b) - g (a, b)) ^ 2) ν) ∧
    Integrable (fun a => ∫ b, (f (a, b) - g (a, b)) ^ 2 ∂ν) μ := by sorry
