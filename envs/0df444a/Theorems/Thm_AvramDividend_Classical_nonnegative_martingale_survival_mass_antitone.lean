-- Prove2me | Theorems.Thm_AvramDividend_Classical_nonnegative_martingale_survival_mass_antitone
-- name    : AvramDividend.Classical.nonnegative_martingale_survival_mass_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:45:48.301653+00:00
-- url     : https://prove2.me/theorems/980abd86-0f47-4cbc-8211-d5a6d6286c94
-- title:
--   Nonnegative martingale mass on decreasing adapted events is antitone
-- statement:
--   Let M be a nonnegative real martingale and S(t) an event measurable at time t, decreasing with t. The expected martingale mass supported on S(u) is no greater than the mass supported on S(t) whenever t ≤ u. This is the finite-horizon Esscher weighted survival monotonicity prerequisite for killed q-scale harmonicity.
-- source:
--   Proof using Mathlib MeasureTheory.Martingale.setIntegral_eq, integral_mono_ae, and set indicator properties. Motivated by the Esscher-transform construction for Avram, Palmowski and Pistorius (2007), optimal dividend problem for a spectrally negative Lévy process.

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.nonnegative_martingale_survival_mass_antitone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M 𝓕 P)
    (hNonneg : ∀ t : ℝ≥0, 0 ≤ᵐ[P] M t)
    (S : ℝ≥0 → Set Ω)
    (hS : ∀ t, MeasurableSet[𝓕 t] (S t))
    (hMono : ∀ t u, t ≤ u → S u ⊆ S t)
    (t u : ℝ≥0) (htu : t ≤ u) :
    (∫ ω, (S u).indicator (M u) ω ∂P) ≤
      (∫ ω, (S t).indicator (M t) ω ∂P) := by sorry
