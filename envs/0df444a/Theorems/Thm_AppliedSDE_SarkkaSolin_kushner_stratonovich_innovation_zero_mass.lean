-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_kushner_stratonovich_innovation_zero_mass
-- name    : AppliedSDE.SarkkaSolin.kushner_stratonovich_innovation_zero_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:54:39.673663+00:00
-- url     : https://prove2.me/theorems/17d3211c-1361-473e-bf0a-79cc7f25dc31
-- title:
--   Nonlinear Kushner–Stratonovich innovation preserves unit probability mass
-- statement:
--   Algorithm 10.6, equations (10.29)–(10.30), printed pp. 206–207. For an integrable, normalised function p and an observation map h with integrable p-weighted first moment, the integral of the nonlinear innovation coefficient (h−E_p[h])p is zero. This algebraic identity holds even for signed p; nonnegativity and full filtering interpretation require separate assumptions. It supplies the mean-zero constraint required for conservation of mass in the Kushner–Stratonovich filtering SPDE. It does not establish stochastic well-posedness of the full KS equation, a distinct outstanding source obligation.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   \int(h(x)-\bar h)\,p(x)\,\mathrm dx=0,\qquad\bar h=\int h(x)p(x)\,\mathrm dx
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Algorithm 10.6, equations (10.29)–(10.30), innovation mass, printed pp. 206–207. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory
open scoped BigOperators

theorem AppliedSDE.SarkkaSolin.kushner_stratonovich_innovation_zero_mass
    (n : ℕ) (p h : (Fin n → ℝ) → ℝ)
    (hpInt : Integrable p)
    (hp : ∫ x : Fin n → ℝ, p x = 1)
    (hhInt : Integrable (fun x => h x * p x)) :
    ∫ x : Fin n → ℝ,
      (h x - ∫ y : Fin n → ℝ, h y * p y) * p x = 0 := by
  sorry
