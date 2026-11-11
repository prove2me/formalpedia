-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18q_original_largejump_Campbell_lintegral_le
-- name    : AvramDividend.Classical.avram_ja18q_original_largejump_Campbell_lintegral_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:46:45.860489+00:00
-- url     : https://prove2.me/theorems/10f73728-b563-4367-8f72-03351c3fb5ea
-- title:
--   Intrinsic original large-negative jump absolute-sum Campbell upper bound
-- statement:
--   On X's ORIGINAL probability space, bound the expected absolute large-negative-jump sum by t times the large-mark first-moment intensity. Use the intrinsic random jump measure, with the mark -1 included.
-- source:
--   AVRAM J-A18 original zero-cutoff Gaussian martingale integrability, 70393ec7 via 37d22393; all on same X and P.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18q_original_largejump_Campbell_lintegral_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0,
      (∫⁻ ω, ‖avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω‖ₑ ∂P) ≤
        (t : ℝ≥0∞) * (∫⁻ z in Iic (-1 : ℝ), ENNReal.ofReal |z| ∂X.ν) := by sorry
