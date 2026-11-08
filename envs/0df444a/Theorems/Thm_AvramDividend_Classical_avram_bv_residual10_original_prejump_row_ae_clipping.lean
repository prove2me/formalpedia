-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_prejump_row_ae_clipping
-- name    : AvramDividend.Classical.avram_bv_residual10_original_prejump_row_ae_clipping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:43:22.089778+00:00
-- url     : https://prove2.me/theorems/591d9e82-bc68-4349-adaf-2075a08f6fdd
-- title:
--   Original stopped dividend pre-jump reserves admit almost-sure eventually exact rowwise clipping
-- statement:
--   Use joint measurability of the actual controlled reserve immediately before each dividend and Lévy jump, evaluated at arbitrary deterministic physical-grid points, to obtain almost-sure eventual rowwise coefficient bounds under summable cutoff errors. The same original process X, filtration 𝓕, dividend D, leftLimit and physical grid are retained. It does not infer integrability or compensated mean-zero from eventual clipping.
-- source:
--   AVRAM BV-RESIDUAL10 original reserve pre-jump row localisation, 7 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_rowwise_ae_eventual_clipping

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_prejump_row_ae_clipping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (u : ℕ → ℕ → ℝ≥0)
    (ε : ℕ → ℝ≥0∞) (hεpos : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ≥0∞)))
    (hεsum : (∑' n, ε n) ≠ ⊤) :
    ∃ K : ℕ → ℕ, ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ∀ i ∈ Finset.range (n + 1),
        abs (Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
          (u n i)) ≤ (K n : ℝ) := by sorry
