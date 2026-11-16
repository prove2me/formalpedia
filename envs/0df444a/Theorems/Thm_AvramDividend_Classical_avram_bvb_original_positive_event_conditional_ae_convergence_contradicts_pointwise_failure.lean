-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_original_positive_event_conditional_ae_convergence_contradicts_pointwise_failure
-- name    : AvramDividend.Classical.avram_bvb_original_positive_event_conditional_ae_convergence_contradicts_pointwise_failure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T15:03:42.765171+00:00
-- url     : https://prove2.me/theorems/b70efd72-56f1-4d64-9ff8-3aae2cf345a5
-- title:
--   Positive-probability physical cash failure contradicts even conditionally almost-everywhere stopped convergence
-- statement:
--   An a.e. convergence assertion restricted to an event E is incompatible with positive probability of E when the original stopped clock is nonzero and every E-path has a genuine nonconvergent physical positive-part error. This isolates the logical end of the source-exact BV zero-contact negation proof.
-- source:
--   An a.e. convergence assertion restricted to an event E is incompatible with positive probability of E when the original stopped clock is nonzero and every E-path has a genuine nonconvergent physical positive-part error. This isolates the logical end of the source-exact BV zero-contact negation proof.

import Mathlib
open Classical MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_original_positive_event_conditional_ae_convergence_contradicts_pointwise_failure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (E : Set Ω) (τ : Ω → ℝ≥0∞)
    (A : ℕ → Ω → ℝ)
    (hPositive : 0 < P E)
    (hSurvive : ∀ ω ∈ E, τ ω ≠ 0)
    (hFails : ∀ ω ∈ E,
      ¬ Tendsto (fun n => max (A n ω) 0) atTop (𝓝 (0 : ℝ)))
    (hAe : ∀ᵐ ω ∂P, ω ∈ E →
      Tendsto (fun n => if τ ω = 0 then 0
        else max (A n ω) 0) atTop (𝓝 (0 : ℝ))) :
    False := by sorry
