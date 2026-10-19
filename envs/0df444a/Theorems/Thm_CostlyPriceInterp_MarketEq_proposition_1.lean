-- Prove2me | Theorems.Thm_CostlyPriceInterp_MarketEq_proposition_1
-- name    : CostlyPriceInterp.MarketEq.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:30.197906+00:00
-- url     : https://prove2.me/theorems/7dbc9260-0a86-4407-b585-e10b17116561
-- title:
--   Proposition 1, pp. 18–19 — a unique linear equilibrium p̃ = a_v ṽ + a_u ũ, α = a_u/a_v the positive root of (18), and a_u > 0
-- statement:
--   Consider the financial-market stage of the costly-interpretation model with standing assumptions $\tau_v,\tau_\xi,\tau_\varepsilon,\tau_e,\tau_u,\tau_\eta,\gamma>0$, where all investors share the sophistication level $\tau_\eta$. A linear equilibrium is a pair $(a_v,a_u)$ with $a_v\ne0$ such that, when investors condition on their private signal, their noisy reading of the price signal $\tilde v + (a_u/a_v)\tilde u$ and their interpretation signal, their aggregate CARA demand at the price
--   $$\tilde p = a_v\tilde v + a_u\tilde u$$
--   is zero for every $(\tilde v,\tilde u)$.
--
--   **Proposition 1.** There exists a unique linear equilibrium. In it, with $\alpha = a_u/a_v$ and $\tau_p = \dfrac{\tau_e\tau_u+(\tau_e+\tau_u)\tau_\eta}{\tau_u+\tau_e(\alpha+1)^2+\alpha^2\tau_\eta}$,
--   1. $a_v = \dfrac{\tau_\varepsilon+\tau_p}{\tau_v+\tau_\varepsilon+\tau_p}$ and $a_u = \dfrac{\tau_p}{\tau_v+\tau_\varepsilon+\tau_p}\cdot\dfrac{\tau_u(\tau_e+\alpha\tau_e+\alpha\tau_\eta)}{\tau_e\tau_u+\tau_e\tau_\eta+\tau_u\tau_\eta}$;
--   2. $\alpha \in \Big(0,\ \dfrac{\tau_e\tau_u}{\tau_e\tau_\varepsilon+\tau_e\tau_\eta+\tau_u\tau_\varepsilon}\Big)$ and $\alpha$ is the unique positive real root of the cubic
--   $$(\tau_e\tau_\varepsilon+\tau_\varepsilon\tau_\eta)\alpha^3 + 2\tau_e\tau_\varepsilon\alpha^2 + (\tau_e\tau_\varepsilon+\tau_e\tau_\eta+\tau_u\tau_\varepsilon)\alpha - \tau_e\tau_u = 0; \qquad (18)$$
--   3. (the note following the proposition) $a_u > 0$.
--
--   The last point is the paper's headline at the trading stage: because interpreting the price is costly, the common interpretation error $\tilde u$ enters the equilibrium price as endogenous noise for every finite sophistication level.
--
--   **Formalization Note** Uniqueness is among all pairs $(a_v,a_u)\in\mathbb R^2$ with $a_v\ne0$, including those with $a_u/a_v\le 0$. The equilibrium predicate is defined from Bayesian demands and market clearing, never from the closed forms; Gaussian conditioning is the linear projection $\Sigma^{-1}c$ and aggregate demand is evaluated at the cross-sectional mean of the signals (see the definition file). The parameters $\gamma$ and $\tau_\xi$ are positive but cancel from the equilibrium.
-- source:
--   Vives & Yang, Costly Interpretation of Asset Prices, SSRN working paper 2763813 (September 2018 version), pp. 18–19 (PDF 20–21), Proposition 1, and the note following it on p. 19 (PDF 21), 'Note that in Proposition 1, we have a_u > 0 for any τ_η ∈ (0, ∞)'

import Mathlib
import Definitions.Def_CostlyPriceInterp_MarketEq_Model

namespace CostlyPriceInterp.MarketEq

/-- Proposition 1, pp. 18–19 (PDF 20–21), with the note following it (p. 19): with a common
sophistication level τ_η there is a unique linear equilibrium price function p̃ = a_v ṽ + a_u ũ; in it
a_v and a_u are the closed forms of the proposition (τ_p of (15) at α), α = a_u/a_v lies in (0, ᾱ) and
is the unique positive root of the cubic (18), and a_u > 0. -/
theorem proposition_1 (P : Params) (hP : P.Standing) :
    (∃! a : ℝ × ℝ, IsLinearEq P a.1 a.2) ∧
    ∀ av au : ℝ, IsLinearEq P av au →
      av = avOf P (au / av) ∧ au = auOf P (au / av) ∧
      0 < au / av ∧ au / av < alphaBar P ∧ cubicF P (au / av) = 0 ∧
      (∀ x : ℝ, 0 < x → cubicF P x = 0 → x = au / av) ∧
      0 < au := by sorry
end CostlyPriceInterp.MarketEq
