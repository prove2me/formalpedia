-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_intrinsic_gaussian_compact_horizon_maximal_L1
-- name    : AvramDividend.Classical.avram_ja18_intrinsic_gaussian_compact_horizon_maximal_L1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T22:04:05.153224+00:00
-- url     : https://prove2.me/theorems/9d747080-b4d4-4a58-aba3-2ec8b61ad796
-- title:
--   Original Gaussian physical source has integrable compact-horizon running maximum
-- statement:
--   An actual intrinsic Gaussian physical residual from the source spectrally negative finite negative activity Lévy process has continuous paths and an integrable supremum of its absolute value on every bounded deterministic horizon. This substantive Doob L2 maximal estimate supplies uniform integrability for true bounded stopping times and is required to apply the already Proved right-continuous optional-sampling theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_ja18_intrinsic_gaussian_compact_horizon_maximal_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun j : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X j t ω)
        atTop (nhds (R t ω)))
    (n : ℕ) (hn : 0 < n) :
    ∃ B : Ω → ℝ,
      Integrable B P ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) →
        ‖R t ω‖ ≤ B ω) := by sorry
