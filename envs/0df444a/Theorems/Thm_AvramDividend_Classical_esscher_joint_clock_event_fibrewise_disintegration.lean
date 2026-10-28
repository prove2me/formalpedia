-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_joint_clock_event_fibrewise_disintegration
-- name    : AvramDividend.Classical.esscher_joint_clock_event_fibrewise_disintegration
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:17:09.821139+00:00
-- url     : https://prove2.me/theorems/1b4e8dda-77d3-437d-89a9-e36758134d66
-- title:
--   True clock-dependent Esscher event probability disintegrates into finite-time tilted section probabilities
-- statement:
--   Let P be a genuine s-finite path measure, η an s-finite real observation clock measure and D a jointly measurable nonnegative density on paths and observation time. For any measurable path-clock event A, its mass under the actual reweighted product measure (P⊗η).withDensity D equals the integral over clock times of the corresponding event-section mass under the genuinely reweighted finite-time path measure P.withDensity D_t. This is an exact Tonelli identity; it does not assume time-independent path laws or the Wiener–Hopf factor.
-- source:
--   Pinned Mathlib MeasureTheory withDensity_apply, lintegral_indicator and lintegral_prod_symm in 0df444a; KKR scale-functions review Esscher finite exponential-time observations.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.esscher_joint_clock_event_fibrewise_disintegration
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    (η : Measure ℝ) [SFinite η]
    (D : Ω × ℝ → ℝ≥0∞) (hD : Measurable D)
    (A : Set (Ω × ℝ)) (hA : MeasurableSet A) :
    ((P.prod η).withDensity D) A =
      (∫⁻ t : ℝ, (P.withDensity (fun ω : Ω => D (ω, t)))
        {ω : Ω | (ω, t) ∈ A} ∂η) := by sorry
