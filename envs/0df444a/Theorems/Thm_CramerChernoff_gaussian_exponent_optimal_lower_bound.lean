-- Prove2me | Theorems.Thm_CramerChernoff_gaussian_exponent_optimal_lower_bound
-- name    : CramerChernoff.gaussian_exponent_optimal_lower_bound
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-23T02:25:36.518727+00:00
-- url     : https://prove2.me/theorems/ac7bc956-a357-47cf-b375-7479f6da997b
-- title:
--   Cramér–Chernoff optimisation: $C\lambda^2-\lambda t\ge-\tfrac{t^2}{4C}$
-- statement:
--   **Cramér–Chernoff optimisation of the Gaussian-shaped MGF bound.** For $C>0$ and all $\lambda\in\mathbb R$, the Chernoff exponent satisfies $C\lambda^2-\lambda t\ge -\tfrac{t^2}{4C}$, with equality at the optimiser $\lambda^\star=\tfrac{t}{2C}$. Equivalently $\inf_{\lambda}\big(C\lambda^2-\lambda t\big)=-\tfrac{t^2}{4C}$, by completing the square $C\lambda^2-\lambda t=C\big(\lambda-\tfrac{t}{2C}\big)^2-\tfrac{t^2}{4C}$.
--
--   **Role in the entropy method.** This is the final Cramér–Chernoff closure step (Boucheron–Lugosi–Massart, *Concentration Inequalities*, §2.3 and the end of the proof of Theorem 5.3). Herbst's argument produces the Gaussian-shaped log-MGF bound $\log\mathbb E e^{\lambda(Z-\mathbb E Z)}\le C\lambda^2$; the exponential Markov inequality (`ProbabilityTheory.measure_ge_le_exp_mul_mgf` in Mathlib) gives $\mathbb P(Z\ge\mathbb E Z+t)\le\exp(C\lambda^2-\lambda t)$ for every $\lambda>0$; minimising the exponent with this lemma yields the sub-Gaussian tail $\mathbb P(Z\ge\mathbb E Z+t)\le e^{-t^2/(4C)}$. Together with the Herbst integration brick this closes the Gaussian half of the entropy method; the Bennett/Bousquet half replaces $C\lambda^2$ by the modified-LSI exponent (the remaining irreducible step).
-- source:
--   Boucheron, Lugosi, Massart, Concentration Inequalities: A Nonasymptotic Theory of Independence, Oxford University Press 2013, Section 2.3 (Cramér–Chernoff method) and end of the proof of Theorem 5.3 (Section 5.2).

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
open Real

theorem CramerChernoff.gaussian_exponent_optimal_lower_bound (C t lam : ℝ) (hC : 0 < C) :
    - t ^ 2 / (4 * C) ≤ C * lam ^ 2 - lam * t := by sorry
