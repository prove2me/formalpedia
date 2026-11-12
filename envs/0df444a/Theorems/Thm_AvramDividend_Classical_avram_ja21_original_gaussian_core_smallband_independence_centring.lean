-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja21_original_gaussian_core_smallband_independence_centring
-- name    : AvramDividend.Classical.avram_ja21_original_gaussian_core_smallband_independence_centring
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T15:03:32.314925+00:00
-- url     : https://prove2.me/theorems/d57f06bf-d0da-45fa-b275-bd64e9b0320c
-- title:
--   Original intrinsic Gaussian core is independent of its compensated jump cutoff, with both source components centered
-- statement:
--   Prove for each n and time t that the concrete original-space fixed Gaussian core R0+Jsmall0 and negative compensated small-band jump Jsmall_n are independent and each has zero mean under the original probability measure. This is the stochastic source-level hypothesis needed to prove physical Gaussian-jump cross-orthogonality. The generic conditional independence-to-zero-covariance step is already Proved (07b1ffd5).
-- source:
--   J-A21 exact physical stochastic independence/centring child of 1e8c653a; reuse Proved original L1 martingale 08823aa3 and compensated mark mean-zero sources where applicable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja21_original_gaussian_core_smallband_independence_centring
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      ProbabilityTheory.IndepFun (fun ω => (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω + avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω)) (fun ω => (-avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)) P ∧
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω + avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω) ∂P) = 0 ∧
      (∫ ω, (-avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) ∂P) = 0 := by sorry
