-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn5_original_allnu_source_reserve_gaussian_jump_decomposition_rightLimit_of_continuity
-- name    : AvramDividend.Classical.avram_wave7_05_turn5_original_allnu_source_reserve_gaussian_jump_decomposition_rightLimit_of_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:27:24.929754+00:00
-- url     : https://prove2.me/theorems/24a84857-b035-42c7-bb9f-c7e846631e22
-- title:
--   Original same-source controlled Gaussian reserve right-limit representation given explicit dividend right-continuity
-- statement:
--   Under the separate no-right-dividend-jump equality hRL, the original reserve's canonical D t subtraction agrees with rightLimit D t. The source Gaussian/jump decomposition remains same Ω/P/𝓕 and explicit.
-- source:
--   Original riskProcess subtracts D t ω, so using rightLimit D t ω demands the explicit hRL hypothesis; hRL is not asserted by IsDividendStrategy alone.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open AvramDividend.Classical MeasureTheory
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn5_original_allnu_source_reserve_gaussian_jump_decomposition_rightLimit_of_continuity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (u : ℝ≥0) (η : Ω),
      X.X u η = (u : ℝ) * X.c +
        (Y.X u η - (u : ℝ) * Y.c) + Jsmall u η + Jlarge u η)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hRL : ∀ (u : ℝ≥0) (η : Ω), rightLimit D u η = D u η)
    (t : ℝ≥0) (ω : Ω) :
    riskProcess X x D t ω =
      x + ((t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) +
          Jsmall t ω + Jlarge t ω) - rightLimit D t ω := by sorry
