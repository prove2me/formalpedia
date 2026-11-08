-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_prejump_inverse_band_exhaustion
-- name    : AvramDividend.Classical.avram_bv_residual10_original_prejump_inverse_band_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T18:56:00.970694+00:00
-- url     : https://prove2.me/theorems/7a0007f8-66b3-4768-a569-0e6d25022ba2
-- title:
--   Original pre-jump physical-row magnitude and reciprocal clipping are measurable and eventually exhaustive
-- statement:
--   For the actual controlled reserve x+X-D, retaining original Lévy process, filtration, dividend strategy and left limits, there are measurable rowwise events on which every physical-grid reserve and its reciprocal are bounded by finite deterministic levels. The events hold eventually almost surely. The reciprocal bound localises all nonzero pre-jump reserves away from the singular zero boundary on each row. The levels may vary with row n and this result does not claim a uniform derivative bound or actual expected mesh-error convergence.
-- source:
--   AVRAM BV-RESIDUAL10 original-process positive-reserve singular-boundary row localisation, 7 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_rowwise_ae_eventual_clipping

open Classical MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_prejump_inverse_band_exhaustion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (u : ℕ → ℕ → ℝ≥0)
    (ε : ℕ → ℝ≥0∞) (hεpos : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ≥0∞)))
    (hεsum : (∑' n, ε n) ≠ ⊤) :
    ∃ N L : ℕ → ℕ, ∃ s : ℕ → Set Ω,
      (∀ n, s n =
        {ω | ∀ i ∈ Finset.range (n + 1),
          abs (Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
            (u n i)) ≤ (N n : ℝ)} ∩
        {ω | ∀ i ∈ Finset.range (n + 1),
          abs ((Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
            (u n i))⁻¹) ≤ (L n : ℝ)}) ∧
      (∀ n, MeasurableSet (s n)) ∧
      (∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n) := by sorry
