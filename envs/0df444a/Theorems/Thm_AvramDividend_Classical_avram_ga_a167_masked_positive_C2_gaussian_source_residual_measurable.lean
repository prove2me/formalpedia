-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a167_masked_positive_C2_gaussian_source_residual_measurable
-- name    : AvramDividend.Classical.avram_ga_a167_masked_positive_C2_gaussian_source_residual_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:36:03.226009+00:00
-- url     : https://prove2.me/theorems/47cd5264-21cc-47f3-b4c6-4b345b970208
-- title:
--   Measurability of finite masked physical Gaussian C2 compensated spatial source with positive active endpoints
-- statement:
--   For any finite measurable active-cell masks and measured original source increment processes, if active initial and prepayment endpoint reserves are positive almost surely and the smooth value has C2 jets continuous on positive reserves, the finite source discounted spatial-minus-Gaussian-compensator residual is a.e. strongly measurable. The source may be the true original X and D, with no Brownian surrogate.
-- source:
--   Generic finite measured source and exact Gaussian drift/hessian compensator algebra, useful for original b0 full-cell Gaussian source a152.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a167_masked_positive_C2_gaussian_source_residual_measurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (w : ℝ → ℝ)
    (hw0 : ContinuousOn w (Ioi (0 : ℝ)))
    (hw1 : ContinuousOn (deriv w) (Ioi (0 : ℝ)))
    (hw2 : ContinuousOn (iteratedDeriv 2 w) (Ioi (0 : ℝ)))
    (m : ℕ)
    (A : ℕ → Ω → Prop) [∀ i, DecidablePred (A i)]
    (hA : ∀ i, MeasurableSet {ω | A i ω})
    (Y R : ℕ → Ω → ℝ)
    (hY : ∀ i, Measurable (Y i))
    (hR : ∀ i, Measurable (R i))
    (hPos : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range m,
      A i ω → 0 < Y i ω ∧ 0 < Y i ω + R i ω)
    (d c σ : ℝ) (E0 E1 : ℕ → ℝ) :
    AEStronglyMeasurable (fun ω =>
      ∑ i ∈ Finset.range m, if A i ω then
        E1 i * (w (Y i ω + R i ω) - w (Y i ω)) -
        (E0 i * (deriv w (Y i ω) * (R i ω - d * c) +
          (iteratedDeriv 2 w (Y i ω) / 2) *
            ((R i ω - d * c)^2 - d * σ^2)) +
          d * E0 i * (σ^2 / 2 * iteratedDeriv 2 w (Y i ω) +
            c * deriv w (Y i ω)))
        else 0) P := by sorry
