-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_fixed_terminal_martingale_early_events
-- name    : AvramDividend.Classical.chat04_esscher_leftshift_fixed_terminal_martingale_early_events
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:17:58.282997+00:00
-- url     : https://prove2.me/theorems/6ce83d56-df53-48a3-acb2-e0cc9502d799
-- title:
--   The compensated negative exponential is a fixed-terminal-measure martingale under the genuine Esscher law
-- statement:
--   For a spectrally negative Lévy process, nonnegative Esscher parameter θ, 0≤ε≤θ, and deterministic times s≤t≤T, the compensated negative exponential Z_r=exp(−εX_r−r(ψ(θ−ε)−ψθ)) has equal integrals over every F_s event under the *same genuine terminal Esscher probability measure Q_T*. This is the precise finite-horizon martingale condition needed to apply the pinned Mathlib Doob maximal inequality on any discretisation up to T. No global Esscher path measure is asserted.
-- source:
--   Combine the accepted compatible finite Esscher laws theorem, the accepted projective left-shift martingale earlier-event identity, the strongly adapted compensated exponential theorem, and the generic transfer theorem for projective martingale event identities to a fixed terminal measure. Each premise is proved directly under the actual original Lévy probability law and finite Esscher densities.

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_projective_martingale_early_events_fixed_terminal_law
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_projective_martingale_early_events
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_compensated_leftshift_reward_strongly_adapted
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_leftshift_fixed_terminal_martingale_early_events
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ ε : ℝ) (hθ : 0 ≤ θ) (hε : 0 ≤ ε) (hεθ : ε ≤ θ)
    (s t T : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕 s) A) :
    (∫ ω in A, Real.exp
       (-ε * X.X s ω -
         (s : ℝ) * (X.ψ (θ - ε) - X.ψ θ)) ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) =
    (∫ ω in A, Real.exp
       (-ε * X.X t ω -
         (t : ℝ) * (X.ψ (θ - ε) - X.ψ θ)) ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) := by sorry
