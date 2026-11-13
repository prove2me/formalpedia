-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB189_original_postpayment_reserve_ae_spatial_levels_null_occupation
-- name    : AvramDividend.Classical.avram_gbB189_original_postpayment_reserve_ae_spatial_levels_null_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T19:13:39.798559+00:00
-- url     : https://prove2.me/theorems/c3553a42-10cd-468b-b741-54ff3fefeaae
-- title:
--   Original postpayment controlled reserve has null occupation at almost every spatial level
-- statement:
--   Original postpayment reserve has zero finite-horizon occupation for Lebesgue-almost every spatial level, simultaneously with P-a.e path for each such level. A sound generic Fubini reduction via B185, B187, B188 and B190; retains the exact original dividend strategy, process and cap-independent stopped reserve. This is an alternate selected-level route and does not claim zero occupation for every fixed level as B100 requires.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB189_original_postpayment_reserve_ae_spatial_levels_null_occupation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (n : ℕ) :
    ∀ᵐ y ∂(volume : Measure ℝ), ∀ᵐ ω ∂P,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧
        x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω = y} = 0 := by sorry
