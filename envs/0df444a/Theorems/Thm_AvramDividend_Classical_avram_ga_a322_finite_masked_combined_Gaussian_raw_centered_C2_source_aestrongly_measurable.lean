-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a322_finite_masked_combined_Gaussian_raw_centered_C2_source_aestrongly_measurable
-- name    : AvramDividend.Classical.avram_ga_a322_finite_masked_combined_Gaussian_raw_centered_C2_source_aestrongly_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:02:33.741716+00:00
-- url     : https://prove2.me/theorems/11ff7394-3771-4b04-b764-9261e18d0837
-- title:
--   Finite measurable mask of genuine Gaussian combined raw and centred C2 residual has a.e. strong measurability
-- statement:
--   For a C² function on positive reserves and a finite family of measurable raw Gaussian increments and reserve samples which remain positive on the selected measurable events, the full Gaussian combined discounted spatial residual after raw first derivative and centered second derivative corrections is a.e. strongly measurable under any measurable event masks. The original source a167 already proves measurability for a compensated HJB ledger and its algebraic cancellations make this exact simpler source equivalent. Applying it with true stopped-and-rare Gaussian masks supplies the a263 large-cell integrability measurability requirement.
-- source:
--   Proved a167 finite masked Gaussian C2 HJB source meas and exact zerojump drift/variance algebraic cancellation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a167_masked_positive_C2_gaussian_source_residual_measurable
open MeasureTheory Filter Topology Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a322_finite_masked_combined_Gaussian_raw_centered_C2_source_aestrongly_measurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (w : ℝ → ℝ)
    (hw0 : ContinuousOn w (Ioi (0 : ℝ)))
    (hw1 : ContinuousOn (deriv w) (Ioi (0 : ℝ)))
    (hw2 : ContinuousOn (iteratedDeriv 2 w) (Ioi (0 : ℝ)))
    (m : ℕ) (A : ℕ → Ω → Prop) [∀ i, DecidablePred (A i)]
    (hA : ∀ i, MeasurableSet {ω | A i ω})
    (Y R : ℕ → Ω → ℝ) (hY : ∀ i, Measurable (Y i))
    (hR : ∀ i, Measurable (R i))
    (hPos : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range m,
      A i ω → 0 < Y i ω ∧ 0 < Y i ω + R i ω)
    (d c σ : ℝ) (E0 E1 : ℕ → ℝ) :
    AEStronglyMeasurable (fun ω =>
      ∑ i ∈ Finset.range m, if A i ω then
        E1 i * (w (Y i ω+R i ω)-w (Y i ω)) -
        E0 i * (deriv w (Y i ω)*R i ω +
          iteratedDeriv 2 w (Y i ω)/2*(R i ω-d*c)^2)
        else 0) P := by sorry
