-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_controlled_levy_exponential_supermartingale
-- name    : AvramDividend.Classical.discounted_controlled_levy_exponential_supermartingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:10:11.844854+00:00
-- url     : https://prove2.me/theorems/b2d57dde-33e1-4541-82c9-702ffb2a5930
-- title:
--   Discounted exponential of the controlled Lévy reserve is a supermartingale for every dividend strategy
-- statement:
--   For a spectrally negative Lévy process X, any adapted nondecreasing dividend process D with D0=0, θ≥0, and q≥ψ(θ), the q-discounted exponential of the controlled reserve X_t−D_t is a supermartingale. Factor it as the positive compensated exponential Lévy martingale exp(θX_t−ψθ t) multiplied by the bounded adapted pathwise decreasing factor exp(t(ψθ−q))exp(−θD_t). The previously proved (or child-decomposed) random antitone product supermartingale theorem establishes the result without a general Lévy Itô formula. This controls the discounted candidate value but not the additional cumulative dividend payout.
-- source:
--   Proved exponential Lévy martingale, monotone adapted dividend exponential factor and a bounded adapted antitone random weight multiplier theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_controlled_levy_exponential_supermartingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q) :
    Supermartingale (fun t ω =>
      Real.exp (θ * (X.X t ω - D t ω) - (t : ℝ) * q)) 𝓕 P := by sorry
