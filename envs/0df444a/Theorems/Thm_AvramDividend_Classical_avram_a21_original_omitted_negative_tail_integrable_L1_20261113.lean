-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_omitted_negative_tail_integrable_L1_20261113
-- name    : AvramDividend.Classical.avram_a21_original_omitted_negative_tail_integrable_L1_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:20:51.167725+00:00
-- url     : https://prove2.me/theorems/0cb3d170-06d7-40b4-b83a-895901761ca1
-- title:
--   Original physical omitted negative compensated near-zero jump tail is integrable
-- statement:
--   Every omitted compensated negative near-zero jump tail Rn-R of the actual original Lévy process is L1 on the ORIGINAL probability space. The Proved source exact omitted-tail L2 moment theorem gives integrable square. The Proved adaptedness of finite cutoff and a.e. measurability of the Gaussian residual-limit field supply strong measurability, and source IsProbabilityMeasure makes MemLp 2 embed into L1.
-- source:
--   Proved 1679c8a4 original omitted tail exact squared L1, 42ada2ca cutoff adapted, 6ad44f7f residual-limit ae adapted, and Mathlib MemLp 2 to Integrable on probability space.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_omitted_negative_tail_integrable_L1_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    ∀ (n : ℕ) (t : ℝ≥0),
      Integrable (fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω) P := by sorry
