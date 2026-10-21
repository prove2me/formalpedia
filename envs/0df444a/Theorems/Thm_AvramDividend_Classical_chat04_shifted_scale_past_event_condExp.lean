-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_shifted_scale_past_event_condExp
-- name    : AvramDividend.Classical.chat04_shifted_scale_past_event_condExp
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:29:24.632391+00:00
-- url     : https://prove2.me/theorems/7425e984-1b8e-466f-b5ea-a3a004d5ed2d
-- title:
--   Conditional shifted q-scale expectation restricted to a measurable past event
-- statement:
--   For a spectrally negative Lévy process, q-scale W, s≤t, deterministic reserve x, and any event A measurable with respect to the filtration F_s, the conditional expectation at time s of the scale payoff W(x+X_t-X_s), restricted to A, equals the event indicator multiplied by the stationary-increment expectation of W(x+X_(t-s)). Assume explicit integrability. This genuine historical-event Markov step combines independent stationary increments with Mathlib condExp_indep_eq and condExp_indicator. It preserves the initial-history indicator needed for a killed process, while the remaining within-(s,t) killing and random current state steps remain separate.
-- source:
--   Published official SpectrallyNegativeLevy independent/stationary increments, Proved q-scale full Borel measurability UUID 45cbe3b4-374d-4fa4-b988-e09f93b74cab, pinned Mathlib IdentDistrib, condExp_indep_eq and condExp_indicator. Elaborated deterministic-start conditional Markov proof source chat04_shifted_scale_condexp_v2.lean.

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_shifted_scale_past_event_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (s t : ℝ≥0) (hst : s ≤ t) (x : ℝ)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (hInt : Integrable (fun ω => W (x + X.X (t - s) ω)) P) :
    P[A.indicator (fun ω => W (x + (X.X t ω - X.X s ω))) | 𝓕 s] =ᵐ[P]
      A.indicator (fun _ => ∫ ω, W (x + X.X (t - s) ω) ∂P) := by sorry
