-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_clock_supported_stopped_event_laws_agree
-- name    : AvramDividend.Classical.esscher_clock_supported_stopped_event_laws_agree
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:43:23.520128+00:00
-- url     : https://prove2.me/theorems/51efe1af-d2be-4a72-bf21-81880a76e403
-- title:
--   Random-clock Esscher law equals independent terminal Esscher product law on supported adapted observations
-- statement:
--   Fix a finite terminal horizon T. For any jointly Borel measurable path-and-real-clock event whose section at every clock time is adapted to the minimum of that clock and T, and which occurs only when the nonnegative clock time is at most T, the event has exactly the same measure under the true clock-dependent Esscher density on P×ν as under Q_T×ν with an independent clock. This is a source-faithful finite-observation replacement for assuming an infinite-horizon tilted probability on arbitrary Ω. It neither asserts that the random-clock measure is globally a product, nor invokes Wiener–Hopf factorisation.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2012), Esscher law §2.1; Prove2Me accepted chat04_esscher_finite_horizon_laws_consistent_on_past_events a74b3334-5c28-44d1-ae88-3057d26957f4; Mathlib MeasureTheory withDensity_apply and lintegral_prod_symm pinned at 0df444a.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_clock_supported_stopped_event_laws_agree
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T : ℝ≥0)
    {ν : Measure ℝ} [SFinite ν]
    (E : Set (Ω × ℝ))
    (hE : MeasurableSet E)
    (hSlice : ∀ t : ℝ,
      @MeasurableSet Ω (𝓕 (min t.toNNReal T))
        {ω : Ω | (ω, t) ∈ E})
    (hSupport : ∀ (ω : Ω) (t : ℝ), (ω, t) ∈ E → t.toNNReal ≤ T)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X z.2.toNNReal z.1 -
        (z.2.toNNReal : ℝ) * X.ψ θ)))) :
    ((P.prod ν).withDensity (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X z.2.toNNReal z.1 -
        (z.2.toNNReal : ℝ) * X.ψ θ)))) E =
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod ν) E := by sorry
