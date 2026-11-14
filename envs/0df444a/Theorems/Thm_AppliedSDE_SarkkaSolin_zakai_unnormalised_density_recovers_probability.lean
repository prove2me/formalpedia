-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_zakai_unnormalised_density_recovers_probability
-- name    : AppliedSDE.SarkkaSolin.zakai_unnormalised_density_recovers_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:54:27.594199+00:00
-- url     : https://prove2.me/theorems/6ef79dbd-d622-441a-b443-41093792f01c
-- title:
--   Zakai unnormalised filtering density yields a normalised probability
-- statement:
--   Algorithm 10.7 and equation (10.32), printed p. 207. If q(x) is a nonnegative integrable unnormalised filter density with positive finite integral Z, its normalisation p=q/Z integrates to one, and any integrable test-observable moment under p is the corresponding moment under q divided by Z. This reproduces exactly the normalisation component of the Zakai/Kushner–Stratonovich relationship. The stochastic Zakai SPDE and nonlinear KS SPDE remain separate, substantial theorem obligations.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   p(x)=\frac{q(x)}{\int q(u)\,\mathrm du},\quad\int p(x)\,\mathrm dx=1
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Algorithm 10.7, equation (10.32), Zakai normalisation, printed p. 207. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory
open scoped BigOperators

theorem AppliedSDE.SarkkaSolin.zakai_unnormalised_density_recovers_probability
    (n : ℕ) (q : (Fin n → ℝ) → ℝ)
    (hqn : ∀ x, 0 ≤ q x) (hqInt : Integrable q)
    (hZ : 0 < ∫ x, q x) :
    let Z : ℝ := ∫ x : Fin n → ℝ, q x
    let p : (Fin n → ℝ) → ℝ := fun x => q x / Z
    (∀ x, 0 ≤ p x) ∧
    (∫ x : Fin n → ℝ, p x = 1) ∧
    (∀ φ : (Fin n → ℝ) → ℝ,
      Integrable (fun x => φ x * q x) →
      ∫ x : Fin n → ℝ, φ x * p x =
        (∫ x : Fin n → ℝ, φ x * q x) / Z) := by
  sorry
