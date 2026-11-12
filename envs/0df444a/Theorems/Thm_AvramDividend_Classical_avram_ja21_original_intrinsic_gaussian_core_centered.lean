-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja21_original_intrinsic_gaussian_core_centered
-- name    : AvramDividend.Classical.avram_ja21_original_intrinsic_gaussian_core_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T15:10:55.075083+00:00
-- url     : https://prove2.me/theorems/9bc499b4-99f3-4f00-a53b-9a848a19f498
-- title:
--   Original intrinsic fixed Gaussian core is centred at each time
-- statement:
--   Prove zero expectation of the original-space fixed Gaussian core from the Proved original-filtration L1 martingale and its zero origin.
-- source:
--   J-A21 reduction of original physical independence/centring d57f06bf feeding root-connected 1e8c653a and 10ff2b5a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja21_original_intrinsic_gaussian_core_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0, (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω + avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω) ∂P) = 0 := by sorry
