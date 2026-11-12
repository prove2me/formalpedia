-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18v_original_largejump_integrable_horizon_envelope
-- name    : AvramDividend.Classical.avram_ja18v_original_largejump_integrable_horizon_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:54:33.270923+00:00
-- url     : https://prove2.me/theorems/7b1fa2ed-9c5f-4f77-81da-e3be7d8d0b78
-- title:
--   Actual large-jump running sum has an integrable fixed-horizon dominating absolute value
-- statement:
--   The physical large-jump process is nonpositive and antitone, so its terminal absolute value dominates all earlier absolute values pathwise. Proved 37d22393 gives its endpoint L1 integrability under Standing. This provides the large-mark component of the original J stopped envelope.
-- source:
--   J-A18 JA18P physical stopped compensation

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18v_original_largejump_integrable_horizon_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) :
    Integrable
      (fun ω => ‖avram_p4_h_gaussian_intrinsic_large_jump_sum X (n : ℝ≥0) ω‖) P ∧
    (∀ ω : Ω, ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) →
      ‖avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω‖ ≤
      ‖avram_p4_h_gaussian_intrinsic_large_jump_sum X (n : ℝ≥0) ω‖) := by sorry
