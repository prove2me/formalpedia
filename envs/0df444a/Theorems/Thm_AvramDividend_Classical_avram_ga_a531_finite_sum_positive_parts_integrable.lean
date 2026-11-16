-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a531_finite_sum_positive_parts_integrable
-- name    : AvramDividend.Classical.avram_ga_a531_finite_sum_positive_parts_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:17:32.359206+00:00
-- url     : https://prove2.me/theorems/a6517416-1290-4b6c-8668-830199dc0f5c
-- title:
--   Finite sum has integrable positive part from integrable positive cell parts
-- statement:
--   For a finite family of almost-everywhere strongly measurable real random variables, integrability of the positive part of every member implies integrability of the positive part of their sum, without any lower-tail integrability assumptions.
-- source:
--   Order bound max(sum f,0) ≤ sum max(f,0), finite-sum integrability and Integrable.mono_nonneg. This avoids invalid assumptions on negative Gaussian tails in a122.

import Mathlib
open MeasureTheory Set Filter Finset
noncomputable section

theorem AvramDividend.Classical.avram_ga_a531_finite_sum_positive_parts_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (S : Finset ℕ) (f : ℕ → Ω → ℝ)
    (hMeas : ∀ i ∈ S, AEStronglyMeasurable (f i) P)
    (hPos : ∀ i ∈ S, Integrable (fun ω => max (f i ω) (0 : ℝ)) P) :
    Integrable (fun ω => max (∑ i ∈ S, f i ω) (0 : ℝ)) P := by sorry
