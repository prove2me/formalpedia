-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin16_gaussian_residual_original_bracket_l2_public
-- name    : AvramDividend.Classical.avram_mix_fin16_gaussian_residual_original_bracket_l2_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-09T13:08:26.223406+00:00
-- url     : https://prove2.me/theorems/892afa4a-32b2-4013-b5d6-478dc12fcd37
-- title:
--   Original intrinsic Gaussian residual has exact σ²t second moment bracket
-- statement:
--   Prove the exact Gaussian bracket from the original source truncations by L2 convergence/isometry and fixed-time residual second moments. No appeal to an unrelated Brownian sample space.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin16_gaussian_residual_original_bracket_l2_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hRadapt : ∀ t : ℝ≥0,
      AEStronglyMeasurable[𝓕.rightCont t] (R t) P) :
    ∀ t : ℝ≥0,
      Integrable (fun ω => (R t ω) ^ 2) P ∧
      (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2 := by sorry
