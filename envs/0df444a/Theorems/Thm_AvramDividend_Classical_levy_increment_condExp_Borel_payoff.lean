-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_Borel_payoff
-- name    : AvramDividend.Classical.levy_increment_condExp_Borel_payoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T14:55:41.036146+00:00
-- url     : https://prove2.me/theorems/c8eb9ff5-e0f7-4b7a-8653-28d84c854efe
-- title:
--   Conditional expectation of an integrable Borel function of a shifted independent Lévy increment
-- statement:
--   Let X be the actual spectrally negative Lévy process on its given filtered probability space, with s≤t. For any deterministic shift x and any Borel measurable payoff f whose shifted stationary increment f(x+X_{t−s}) is integrable, the conditional expectation E[f(x+X_t−X_s)|F_s] is the constant E[f(x+X_{t−s})]. Use the stated independence of the increment X_t−X_s from the past F_s and its stationary distribution, transfer measurable functions through comap sigma algebras and IdentDistrib.comp, transfer integrability, and apply the pinned Mathlib condExp_indep_eq. This generalises the existing proof pattern from Chat 04 (shifted q-scale payoff) to arbitrary measurable f; it is a genuinely stochastic semigroup interface for a deterministic starting reserve. It does not claim the random-current-state Markov property, the general Lévy generator limit or the controlled stopped HJB budget.
-- source:
--   Adapt the source-faithful Chat04 shifted-scale conditional expectation proof using the exact Lévy structure, with arbitrary Measurable f in place of the scale-function measurability lemma; no Open imports.

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_increment_condExp_Borel_payoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (x : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hInt : Integrable (fun ω => f (x + X.X (t - s) ω)) P) :
    P[(fun ω => f (x + (X.X t ω - X.X s ω))) | 𝓕 s] =ᵐ[P]
      (fun _ => ∫ ω, f (x + X.X (t - s) ω) ∂P) := by sorry
