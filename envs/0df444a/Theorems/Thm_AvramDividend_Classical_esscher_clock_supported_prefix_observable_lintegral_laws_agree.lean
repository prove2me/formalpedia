-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_clock_supported_prefix_observable_lintegral_laws_agree
-- name    : AvramDividend.Classical.esscher_clock_supported_prefix_observable_lintegral_laws_agree
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:01:43.052541+00:00
-- url     : https://prove2.me/theorems/ba79d3dc-2d63-4429-9384-23e5a5b5f1f5
-- title:
--   Any nonnegative supported clock-prefix reward has equal realised-clock and fixed-terminal Esscher product integrals
-- statement:
--   For an adapted supported event E of a clock t≤T and any measurable clock-prefix observable Y with adapted fixed-clock inverse images, the nonnegative Lebesgue integral of every measurable reward g(Y) over E under the realised-clock density (P×ν).withDensity M_clock equals the integral under the genuine independent product Q_T×ν. This holds even if both integrals are infinite. It does not assert an unrestricted product law for the realised-time density.
-- source:
--   Apply the accepted supported clock-prefix observable map transfer (prospective public theorem esscher_clock_supported_prefix_observable_map_laws_agree) and Mathlib lintegral_map at both restricted measures. The imported map theorem itself derives from accepted clock supported event law 51efe1af and asserts no Wiener–Hopf independence.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_clock_supported_prefix_observable_map_laws_agree

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_clock_supported_prefix_observable_lintegral_laws_agree
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (T : ℝ≥0)
    {ν : Measure ℝ} [SFinite ν]
    (E : Set (Ω × ℝ)) (hE : MeasurableSet E)
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
        {ω : Ω | Y (ω, t) ∈ B})
    (g : β → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ z in E, g (Y z) ∂
      ((P.prod ν).withDensity (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X z.2.toNNReal z.1 -
          (z.2.toNNReal : ℝ) * X.ψ θ))))) =
    (∫⁻ z in E, g (Y z) ∂
      ((P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod ν)) := by sorry
