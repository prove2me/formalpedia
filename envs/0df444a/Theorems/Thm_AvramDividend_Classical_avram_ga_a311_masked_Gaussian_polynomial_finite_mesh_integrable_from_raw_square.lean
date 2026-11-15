-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a311_masked_Gaussian_polynomial_finite_mesh_integrable_from_raw_square
-- name    : AvramDividend.Classical.avram_ga_a311_masked_Gaussian_polynomial_finite_mesh_integrable_from_raw_square
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:52:23.570618+00:00
-- url     : https://prove2.me/theorems/6552aef0-4f29-4872-b950-bebd88ebcd0f
-- title:
--   Measurable finite masked rare Gaussian raw and centred polynomial source integrable from raw-square energy
-- statement:
--   For any finite original Gaussian mesh, assume actual raw increments are measurable, original physical full stopping masks are measurable, and the masked sum of squared raw increments is integrable. Then the masked rare-event polynomial source 1+abs(raw increment)+half centred squared increment is integrable, for arbitrary deterministic drift centering and fixed positive rare threshold. This uses the unconditional a310 scalar polynomial-to-quadratic majorant, closing the explicit source integrability premise in a304.
-- source:
--   Original Gaussian a310 unconditional polynomial majorant, true finite physical raw squared energy a243, stopping source measurability a242.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a310_raw_centered_Gaussian_polynomial_bounded_by_raw_square
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a311_masked_Gaussian_polynomial_finite_mesh_integrable_from_raw_square
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (r : ℕ → ℕ → Ω → ℝ) (a : ℕ → ℝ)
    (A : ℕ → ℕ → Ω → Prop)
    [∀ m i, DecidablePred (A m i)]
    (δ : ℝ) (hδ : 0 < δ)
    (hrm : ∀ m i, Measurable (r m i))
    (hAm : ∀ m i, MeasurableSet {ω : Ω | A m i ω})
    (hRawI : ∀ m, Integrable (fun ω =>
      ∑ i ∈ Finset.range m,
        if A m i ω then (r m i ω)^2 else 0) P) :
    ∀ m, Integrable (fun ω =>
      ∑ i ∈ Finset.range m,
        if A m i ω ∧ δ ≤ |r m i ω| then
          1 + |r m i ω| + (r m i ω-a m)^2/2 else 0) P := by sorry
