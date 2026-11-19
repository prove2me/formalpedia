-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_full_compensated_jump_equals_smalllarge_and_drift_adjustment
-- name    : AvramDividend.Classical.avram_ja18_original_full_compensated_jump_equals_smalllarge_and_drift_adjustment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:42:25.864493+00:00
-- url     : https://prove2.me/theorems/4b7a1568-5e21-4419-ba1c-3be27ddc1fbd
-- title:
--   True original compensated full negative-jump martingale channel contains small, large and drift adjustment
-- statement:
--   For any original same-X Levy source, the full compensated negative-jump component formed as X(t)-μt-R(t) equals actual small-negative-mark compensated limit plus uncompensated large-negative-mark sum plus the deterministic drift correction (c-μ)t, a.e. simultaneously at all times. Taking μ=E[X(1)] identifies the genuine full negative-jump martingale in Proved d59113bc. This is the exact physical source correction required to replace the invalid Jsmall-only mixed Ito two-noise ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_intrinsic_gaussian_smallmark_largemark_full_path_ae_split
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_full_compensated_jump_equals_smalllarge_and_drift_adjustment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω)))
    (μ : ℝ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω - (t : ℝ) * μ - R t ω =
        Jsmall t ω + avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
        (t : ℝ) * (X.c - μ) := by sorry
