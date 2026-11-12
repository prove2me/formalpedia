-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja19_original_finite_activity_smallband_uniform_L2_count_envelope
-- name    : AvramDividend.Classical.avram_ja19_original_finite_activity_smallband_uniform_L2_count_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:47:07.855202+00:00
-- url     : https://prove2.me/theorems/c64684fd-5c33-4f91-ae2e-d39a30619b1f
-- title:
--   Uniform squared-integrable physical compensated small-band envelope under finite negative activity
-- statement:
--   On the original Omega and probability measure, the total count of negative jumps up to T is square-integrable. All compensated small-band jumps have marks of size at most one, while the deterministic compensator is bounded by T times the finite total negative Levy mass. Thus the entire nested cutoff family at all times up to T is bounded by one common random variable with an integrable square. Use proved finite count L2 a6562a4d, finite-jump sum identity 1c1d4731, and existing L1 envelope b3763297.
-- source:
--   J-A19 original-space finite-activity count L2 route

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja19_original_finite_activity_smallband_uniform_L2_count_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ T : ℝ≥0, ∃ B : Ω → ℝ,
      Integrable (fun ω => (B ω) ^ 2) P ∧
      (∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t : ℝ≥0, t ≤ T →
        ‖avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω‖ ≤ B ω) := by sorry
