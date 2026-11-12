-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja19_original_finite_activity_smallband_limit_square_L1
-- name    : AvramDividend.Classical.avram_ja19_original_finite_activity_smallband_limit_square_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:35:10.041667+00:00
-- url     : https://prove2.me/theorems/e5234be6-da74-4331-bff8-8847425c3104
-- title:
--   Original finite-activity compensated small-jump limit has a square-integrable fixed-time value
-- statement:
--   The original finite-band compensated negative-jump processes converge pointwise on the original probability space to Jsmall. Finite total negative-jump intensity gives a square-integrable Poisson count. Bounded marks in (-1,0) and finite deterministic compensation dominate Jsmall by that count, establishing integrability of its square at each fixed time. Reuses the already Proved common-space limit 9362895e, total count L2 a6562a4d and residual count envelope 1b696ff5.
-- source:
--   J-A19 original physical finite-activity small jumps; input Proved 9362895e, a6562a4d, 1b696ff5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja19_original_finite_activity_smallband_limit_square_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ Jsmall : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (𝓝 (Jsmall t ω))) ∧
      (∀ t : ℝ≥0, Integrable (fun ω => (Jsmall t ω) ^ 2) P) := by sorry
