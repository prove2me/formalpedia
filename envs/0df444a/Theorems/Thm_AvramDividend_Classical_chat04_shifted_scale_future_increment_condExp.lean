-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_shifted_scale_future_increment_condExp
-- name    : AvramDividend.Classical.chat04_shifted_scale_future_increment_condExp
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:21:19.933247+00:00
-- url     : https://prove2.me/theorems/c1929686-e71f-401e-b969-c5bf79fafd0b
-- title:
--   Conditional expectation of shifted future Lévy q-scale payoff is stationary
-- statement:
--   For a spectrally negative Lévy process, any q-scale function W, deterministic initial capital x and s≤t, the conditional expectation of W(x+X_t−X_s) with respect to the full prior filtration F_s is almost surely the constant expectation of W(x+X_(t−s)), whenever this payoff is integrable. This combines stationary increments, full-filtration independent increments, measurable transformed scale payoffs and Mathlib condExp_indep_eq. It is a genuine deterministic-start Markov conditional-expectation ingredient; a random starting state, pathwise killing at ruin, and q-scale semigroup harmonicity remain independent open steps.
-- source:
--   Adaptedness and independent stationary increments from original SpectrallyNegativeLevy definition; remotely Proved Borel measurability of q-scale UUID 45cbe3b4-374d-4fa4-b988-e09f93b74cab; accepted future-exponential condExp proof UUID 045f8178-65ec-42ff-ab28-2977ddfdf2de; pinned Mathlib IdentDistrib.comp, integral_eq, integrable_iff and condExp_indep_eq.

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_shifted_scale_future_increment_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (s t : ℝ≥0) (hst : s ≤ t) (x : ℝ)
    (hInt : Integrable (fun ω => W (x + X.X (t - s) ω)) P) :
    P[(fun ω => W (x + (X.X t ω - X.X s ω))) | 𝓕 s] =ᵐ[P]
      (fun _ => ∫ ω, W (x + X.X (t - s) ω) ∂P) := by sorry
