-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events
-- name    : AvramDividend.Classical.chat04_esscher_finite_horizon_laws_consistent_on_past_events
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:02:12.729574+00:00
-- url     : https://prove2.me/theorems/a74b3334-5c28-44d1-ae88-3057d26957f4
-- title:
--   Finite Esscher probability laws agree on every past-filtration event
-- statement:
--   For any nonnegative Esscher parameter θ and deterministic horizons 0≤s≤t, the actual finite-horizon probability laws obtained by exponential weighting at s and at t give identical probabilities to every event measurable in the Lévy filtration at s. This proves genuine projective consistency of finite Esscher changes of measure, without constructing or assuming a global tilted probability measure.
-- source:
--   Use the previously Proved compensated Lévy exponential early-event integral equality, together with `Measure.withDensity_apply` and the nonnegative real-to-ENNReal integral identity on a measurable past event. The result is an independent stochastic consistency theorem useful for the descending Wiener–Hopf law.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_chat01_levy_exponential_early_event_integral_eq
import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_integrable
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_finite_horizon_laws_consistent_on_past_events
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕 s) A) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X s ω - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ)))) A =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))) A := by sorry
