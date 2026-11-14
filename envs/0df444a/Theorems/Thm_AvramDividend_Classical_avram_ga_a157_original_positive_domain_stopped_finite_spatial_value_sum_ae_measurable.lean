-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a157_original_positive_domain_stopped_finite_spatial_value_sum_ae_measurable
-- name    : AvramDividend.Classical.avram_ga_a157_original_positive_domain_stopped_finite_spatial_value_sum_ae_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:27:59.49221+00:00
-- url     : https://prove2.me/theorems/99d24b55-6c63-4c18-81ce-1f4c0301e549
-- title:
--   Actual stopped Gaussian finite m-cell spatial value increment sum is a.e. strongly measurable using original strictly positive source-or-inactive endpoint alternative
-- statement:
--   For any physically stopped finite Gaussian source grid with measurable original prepayment/postpayment reserves and exponential discount, if the source states in each cell are almost surely either equal or both strictly positive, then the finite sum of discounted spatial value increments is a.e. strongly measurable for a value function continuous only on the positive reserves. Construct a continuous positive-domain zero-extension and use pointwise cancellation of identical source endpoints outside that domain; the result closes a critical measurability component of the original b0 positive-root and full-cell ga152 without asserting global measurability or smoothness of w.
-- source:
--   Proved original Gaussian stopped source cell state alternative ga43 plus pinned Mathlib continuous-piecewise measurable extension and Finset.aestronglyMeasurable_sum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a157_original_positive_domain_stopped_finite_spatial_value_sum_ae_measurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ioi (0 : ℝ)))
    (m : ℕ) (Y Z E : ℕ → Ω → ℝ)
    (hY : ∀ i, Measurable (Y i)) (hZ : ∀ i, Measurable (Z i))
    (hE : ∀ i, Measurable (E i))
    (hAlt : ∀ i, ∀ᵐ ω ∂P, Y i ω = Z i ω ∨
      (0 < Y i ω ∧ 0 < Z i ω)) :
    AEStronglyMeasurable (fun ω =>
      ∑ i ∈ Finset.range m, E i ω * (w (Z i ω) - w (Y i ω))) P := by sorry
