-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_clock_supported_prefix_observable_map_laws_agree
-- name    : AvramDividend.Classical.esscher_clock_supported_prefix_observable_map_laws_agree
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:54:45.494474+00:00
-- url     : https://prove2.me/theorems/7b9632b6-e87b-4fca-a85e-2e10801c7b59
-- title:
--   Supported clock-prefix observable pushforward laws agree under realised-clock density and fixed-terminal Esscher product
-- statement:
--   Fix a deterministic terminal T, an arbitrary S-finite real-valued clock law ν, a measurable clock-prefix event E supported on clock values at or before T with adapted deterministic-time fibres, and an arbitrary measurable clock-prefix observable Y whose measurable inverse images have adapted clock fibres. The entire distribution of Y restricted to E under the realised-clock density (P×ν).withDensity M_clock equals its distribution restricted to E under the genuine product Q_T×ν. This is a full measure-valued supported clock-prefix transfer, without identifying the unrestricted realised-clock density with an independent product.
-- source:
--   Use accepted esscher_clock_supported_stopped_event_laws_agree UUID 51efe1af, applying it to each supported measurable event (Y⁻¹B)∩E; Mathlib Measure.ext, Measure.map_apply and restrict_apply. No global Q∞, independent clock under realised density, WH, exit or killed-scale hypotheses.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_clock_supported_stopped_event_laws_agree

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_clock_supported_prefix_observable_map_laws_agree
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
    (hSupport : ∀ (ω : Ω) (t : ℝ),
      (ω, t) ∈ E → t.toNNReal ≤ T)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X z.2.toNNReal z.1 -
        (z.2.toNNReal : ℝ) * X.ψ θ))))
    {β : Type*} [MeasurableSpace β]
    (Y : (Ω × ℝ) → β) (hY : Measurable Y)
    (hYslice : ∀ (B : Set β), MeasurableSet B →
      ∀ t : ℝ, @MeasurableSet Ω (𝓕 (min t.toNNReal T))
        {ω : Ω | Y (ω, t) ∈ B}) :
    Measure.map Y
      (((P.prod ν).withDensity (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X z.2.toNNReal z.1 -
          (z.2.toNNReal : ℝ) * X.ψ θ)))).restrict E) =
    Measure.map Y
      (((P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod ν).restrict E) := by sorry
