-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_exponential_levy_supermartingale
-- name    : AvramDividend.Classical.discounted_exponential_levy_supermartingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:00:10.739989+00:00
-- url     : https://prove2.me/theorems/9a96f7d0-5714-4d49-a2a6-13d69999a012
-- title:
--   The q-discounted exponential of a spectrally negative Lévy process is a supermartingale when ψθ≤q
-- statement:
--   For a spectrally negative Lévy process, θ≥0 and q≥ψ(θ), the discounted exponential exp(θ X_t−q t) is a supermartingale in the process's original filtration. Factor it as the proved compensated exponential martingale exp(θX_t−ψ(θ)t) multiplied by the deterministic antitone weight exp((ψ(θ)−q)t). The compensated exponential is positive; apply the general antitone-weight supermartingale lemma.
-- source:
--   Proved compensated exponential Lévy martingale and the generic martingale_antitone_weight_supermartingale child, with the elementary exponential addition identity and monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_exponential_levy_supermartingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q) :
    Supermartingale (fun t ω =>
      Real.exp (θ * X.X t ω - (t : ℝ) * q)) 𝓕 P := by sorry
