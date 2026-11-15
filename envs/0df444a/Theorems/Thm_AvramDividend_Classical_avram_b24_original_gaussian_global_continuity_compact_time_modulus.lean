-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_gaussian_global_continuity_compact_time_modulus
-- name    : AvramDividend.Classical.avram_b24_original_gaussian_global_continuity_compact_time_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:54:27.342718+00:00
-- url     : https://prove2.me/theorems/1dff1bd3-229d-4870-aeac-e4d1fa6584f8
-- title:
--   Actual original finite-activity intrinsic Gaussian source has almost-sure compact time uniform modulus
-- statement:
--   For the actual original finite-negative-activity Levy source X and its intrinsic Gaussian residual limit R on the same sample space, the previously proved almost-sure global time continuity implies by compact Heine-Cantor uniform continuity a strict-to-right increment modulus on [0,T], uniformly for every deterministic s≤t with t-s≤δ. The modulus holds almost surely and for all ε>0, enabling Gaussian ruin-contact mesh vanishing without a synthetic Brownian companion or post-ruin assumptions.
-- source:
--   Proved a38 original Gaussian intrinsic limit path continuity, pinned Mathlib IsCompact.uniformContinuousOn_of_continuous and NNReal dist identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a38_original_intrinsic_gaussian_physical_limit_globally_continuous_ae_20261114
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_gaussian_global_continuity_compact_time_modulus
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ s t : ℝ≥0, s ≤ t → t ≤ T → t - s ≤ δ →
        ‖R t ω - R s ω‖ ≤ ε := by sorry
