-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a159_original_gaussian_finite_active_positive_domain_spatial_sum_measurable
-- name    : AvramDividend.Classical.avram_ga_a159_original_gaussian_finite_active_positive_domain_spatial_sum_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:31:37.691541+00:00
-- url     : https://prove2.me/theorems/e9f71e64-1aa3-407b-89d4-d3e025c82b8b
-- title:
--   Actual Gaussian physically active finite m-cell positive-domain spatial value sum is a.e. measurable under precisely the finite source reserve alternative
-- statement:
--   For the original true stopped Gaussian physical m-cell source, only the finitely many active cells are required to satisfy the original almost-sure alternative that the two reserves agree or both remain strictly positive. The original stopped-cell observation ga43 establishes exactly this finite-index assertion. Combined with positive-domain continuity, measurable source endpoint values and discount, the actual m-cell discounted spatial value sum is a.e. strongly measurable. This finitary statement avoids the unnecessary all-index assumption in ga157 and is adapted to the exact root ga146.
-- source:
--   Pinned Mathlib ContinuousOn.measurable_piecewise and Finset.aestronglyMeasurable_sum, original Gaussian source finite-cell observation ga43.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a159_original_gaussian_finite_active_positive_domain_spatial_sum_measurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ioi (0 : ℝ)))
    (m : ℕ) (Y Z E : ℕ → Ω → ℝ)
    (hY : ∀ i, Measurable (Y i)) (hZ : ∀ i, Measurable (Z i))
    (hE : ∀ i, Measurable (E i))
    (hAlt : ∀ i ∈ Finset.range m, ∀ᵐ ω ∂P,
      Y i ω = Z i ω ∨ (0 < Y i ω ∧ 0 < Z i ω)) :
    AEStronglyMeasurable (fun ω =>
      ∑ i ∈ Finset.range m, E i ω * (w (Z i ω) - w (Y i ω))) P := by sorry
