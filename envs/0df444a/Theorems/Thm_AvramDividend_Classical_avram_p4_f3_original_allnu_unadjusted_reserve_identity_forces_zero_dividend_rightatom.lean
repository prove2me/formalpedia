-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_allnu_unadjusted_reserve_identity_forces_zero_dividend_rightatom
-- name    : AvramDividend.Classical.avram_p4_f3_original_allnu_unadjusted_reserve_identity_forces_zero_dividend_rightatom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:13:22.737678+00:00
-- url     : https://prove2.me/theorems/86ec90b8-49b4-4912-8098-561e8f0f04fe
-- title:
--   Unadjusted all-ν riskProcess source identity forces zero dividend right-jump
-- statement:
--   Under the original Lévy source split, if the unadjusted pre-right-dividend riskProcess is claimed to equal the post-right-dividend reserve, the payment right atom must vanish. Thus the unadjusted all-ν identity cannot handle arbitrary admissible right-jump dividend strategies; the exact corrected identity must retain the atom.
-- source:
--   Definitional unfolding of riskProcess and source split, followed by real arithmetic.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_allnu_unadjusted_reserve_identity_forces_zero_dividend_rightatom
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
    (t : ℝ≥0) (ω : Ω)
    (hUnadjusted :
      riskProcess X x D t ω =
        x + ((t : ℝ) * X.c +
          (Y.X t ω - (t : ℝ) * Y.c) +
          Jsmall t ω + Jlarge t ω) - rightLimit D t ω) :
    rightLimit D t ω = D t ω := by sorry
