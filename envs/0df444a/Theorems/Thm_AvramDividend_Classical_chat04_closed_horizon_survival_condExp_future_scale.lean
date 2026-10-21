-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_closed_horizon_survival_condExp_future_scale
-- name    : AvramDividend.Classical.chat04_closed_horizon_survival_condExp_future_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T21:35:49.713405+00:00
-- url     : https://prove2.me/theorems/f7115442-c242-442d-af84-ea77e06f8286
-- title:
--   Conditional future q-scale payoff on genuine continuous-time survival through T
-- statement:
--   Under the original spectrally negative Lévy Standing assumptions and positive discount q, take any two deterministic times T≤u, arbitrary upper/lower strict reserve barriers, and actual survival through every continuous time t≤T (including the endpoint). Conditional on F_T, the canonical q-scale payoff W(x+X_u−X_T) restricted to that historical survival event has conditional expectation equal to the same event indicator multiplied by the stationary unconditional expected scale payoff W(x+X_(u−T)). The continuous-horizon survival event is shown F_T-measurable by an existing accepted theorem and fixed-time scale integrability is guaranteed by an accepted Standing-case theorem. This is the exact path-history conditional Markov identity needed before introducing future interval killing in the stopped-scale proof. It does not assert the killed q-harmonicity martingale.
-- source:
--   Proved chat04_closed_horizon_survival_filtration_measurable UUID 8f46ff43-afd6-449a-be49-308c7399740e and chat04_standing_past_event_scale_condExp UUID 3b6d30d3-f850-4855-b55f-b19339f58174.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_closed_horizon_survival_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_standing_past_event_scale_condExp

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_closed_horizon_survival_condExp_future_scale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower upper : ℝ)
    (T u : ℝ≥0) (hTu : T ≤ u) (x : ℝ) :
    P[({ω | ∀ t : ℝ≥0, t ≤ T →
       ¬ (X.X t ω < lower ∨ upper < X.X t ω)}).indicator
        (fun ω => W (x + (X.X u ω - X.X T ω))) | 𝓕 T] =ᵐ[P]
      ({ω | ∀ t : ℝ≥0, t ≤ T →
       ¬ (X.X t ω < lower ∨ upper < X.X t ω)}).indicator
        (fun _ => ∫ ω, W (x + X.X (u - T) ω) ∂P) := by sorry
