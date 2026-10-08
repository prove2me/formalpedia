-- Prove2me | Theorems.Thm_AvramDividend_Classical_martingale_bounded_adapted_antitone_weight_supermartingale
-- name    : AvramDividend.Classical.martingale_bounded_adapted_antitone_weight_supermartingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:08:59.776258+00:00
-- url     : https://prove2.me/theorems/c1efb6e8-facc-4794-8115-5b3edc9c6521
-- title:
--   A nonnegative martingale times a bounded adapted decreasing random factor is a supermartingale
-- statement:
--   Let f be a nonnegative real-valued martingale and w a bounded real-valued process adapted to the same filtration, with 0≤w_t≤1 and nonincreasing paths. Then w_t f_t is a supermartingale. At s≤t, the product inequality w_t f_t≤w_s f_t and conditional-expectation monotonicity give E[w_t f_t|F_s]≤E[w_s f_t|F_s]. Adaptedness allows w_s to be pulled out, yielding w_s f_s. Integrability follows from bounded multiplication. This bridges the positive exponential Lévy martingale to the decreasing dividend factor exp(−θD_t).
-- source:
--   Pinned Mathlib condExp_mono, condExp_mul_of_aestronglyMeasurable_left, Integrable.bdd_mul and martingale conditional expectation identity.

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.martingale_bounded_adapted_antitone_weight_supermartingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (f : ℝ≥0 → Ω → ℝ) (hf : Martingale f 𝓕 μ)
    (hpos : ∀ t : ℝ≥0, ∀ᵐ ω ∂μ, 0 ≤ f t ω)
    (w : ℝ≥0 → Ω → ℝ)
    (hwadapt : Adapted 𝓕 w)
    (hwbdd : ∀ t ω, 0 ≤ w t ω ∧ w t ω ≤ 1)
    (hwanti : ∀ ω, Antitone (fun t => w t ω)) :
    Supermartingale (fun t ω => w t ω * f t ω) 𝓕 μ := by sorry
