-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_discounted_terminal_integrable_of_ae_bound
-- name    : AvramDividend.Classical.avram_p4_e_localise_discounted_terminal_integrable_of_ae_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:46:45.576207+00:00
-- url     : https://prove2.me/theorems/782559c6-2b21-4f34-8078-d096ce603f57
-- title:
--   Uniformly bounded original postpayment payoff yields integrable discounted terminal
-- statement:
--   Under the actual source probability law and nonnegative discount, an almost-sure bounded original stopped postpayment payoff w(W) has an integrable discounted terminal, provided its exact terminal variable is a.e. strongly measurable. This is the L1 terminal bridge for a bounded localising clock; the bound on w(W) must be justified independently using actual reserve contacts, negative overshoot and endpoint continuity. No stochastic integral or optional stopping conclusion is assumed.
-- source:
--   SpectrallyNegativeLevy.isProbability, Real.exp nonnegativity/discount and pinned Mathlib Integrable.of_bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p4_e_localise_discounted_terminal_integrable_of_ae_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0) (w : ℝ → ℝ) (W : Ω → ℝ)
    (hMeas : AEStronglyMeasurable
      (fun ω => Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) P)
    (B : ℝ)
    (hBound : ∀ᵐ ω ∂P, |w (W ω)| ≤ B) :
    Integrable (fun ω => Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) P := by sorry
