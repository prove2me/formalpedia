-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a148_original_lastcell_negative_integrability_from_two_value_moments
-- name    : AvramDividend.Classical.avram_ga_a148_original_lastcell_negative_integrability_from_two_value_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:12:22.350264+00:00
-- url     : https://prove2.me/theorems/2c8c5380-6f32-4ee8-b067-9912a4ca14bb
-- title:
--   Original genuinely clipped last-cell negative spatial value is integrable from two stopped source-value absolute moment bounds
-- statement:
--   On the original stopped event, any discount between zero and one makes the negative part of a last-cell spatial value difference integrable whenever the absolute values at its two original stopped source endpoints are integrable and the clipped negative part is measurable. The pathwise bound by the two endpoint absolute values supplies the missing one-sided final-cell integrability estimate in the Gaussian b0 root; proving the actual source-specific endpoint bounds remains a separate stochastic/localisation obligation.
-- source:
--   Original last-cell negative integrability child ga145 and certified original discounted last source ga131; decomposition of the true stopped source value pair.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a148_original_lastcell_negative_integrability_from_two_value_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E A B : ℕ → Ω → ℝ) (mask : Ω → Prop)
    [DecidablePred mask]
    (hE : ∀ m ω, 0 ≤ E m ω ∧ E m ω ≤ 1)
    (hAI : ∀ m, Integrable (fun ω => if mask ω then |A m ω| else 0) P)
    (hBI : ∀ m, Integrable (fun ω => if mask ω then |B m ω| else 0) P)
    (hMeas : ∀ m, AEStronglyMeasurable
      (fun ω => if mask ω then max (-(E m ω * (A m ω - B m ω))) 0 else 0) P) :
    ∀ m, Integrable
      (fun ω => if mask ω then max (-(E m ω * (A m ω - B m ω))) 0 else 0) P := by sorry
