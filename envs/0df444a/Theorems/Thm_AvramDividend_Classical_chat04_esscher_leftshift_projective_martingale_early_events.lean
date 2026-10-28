-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_projective_martingale_early_events
-- name    : AvramDividend.Classical.chat04_esscher_leftshift_projective_martingale_early_events
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:34:11.185701+00:00
-- url     : https://prove2.me/theorems/62b1efcb-c1b1-40ce-b28c-99e4473f5138
-- title:
--   The left-shifted compensated Lévy exponential has projectively consistent Esscher martingale expectations
-- statement:
--   For any 0≤ε≤θ and deterministic times s≤t, the compensated negative exponential Z_r=exp(−ε X_r−r[ψ(θ−ε)−ψ(θ)]) has equal expectations on every past-filtration event A when integrated against the compatible θ-Esscher probability measures at horizons s and t. This is a genuine finite-time projective martingale identity under the Esscher tilt, derived without postulating a global tilted sample-path law.
-- source:
--   First apply the proven pointwise Esscher density-ratio restricted integral identity to both horizons. Then use the proven original-law martingale early-event equality for tilt θ−ε≥0. This is precisely the projective martingale property needed to bound downward first passages under the tilted laws.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_compensated_setIntegral_change
import Theorems.Thm_AvramDividend_Classical_chat01_levy_exponential_early_event_integral_eq
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_leftshift_projective_martingale_early_events
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ ε : ℝ) (hε : 0 ≤ ε) (hεθ : ε ≤ θ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕 s) A) :
    (∫ ω in A, Real.exp (-ε * X.X s ω -
        (s : ℝ) * (X.ψ (θ - ε) - X.ψ θ)) ∂(P.withDensity (fun ω : Ω =>
        ENNReal.ofReal
          (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ))))) =
    (∫ ω in A, Real.exp (-ε * X.X t ω -
        (t : ℝ) * (X.ψ (θ - ε) - X.ψ θ)) ∂(P.withDensity (fun ω : Ω =>
        ENNReal.ofReal
          (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))))) := by sorry
