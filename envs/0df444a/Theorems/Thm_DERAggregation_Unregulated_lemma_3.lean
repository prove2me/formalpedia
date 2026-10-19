-- Prove2me | Theorems.Thm_DERAggregation_Unregulated_lemma_3
-- name    : DERAggregation.Unregulated.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:25:05.532652+00:00
-- url     : https://prove2.me/theorems/3f82ebd0-db6d-4dca-bba9-10e2084355ee
-- title:
--   Lemma 3, p. 10 — the prosumer's optimal response to a two-part offer
-- statement:
--   Consider one prosumer with utility $u$, capacity $C$ and consumption bound $Z$ satisfying Assumption 1, facing the wholesale price $\lambda$ and an aggregator's two-part offer: participation fee $P\ge0$ and unit price $p$ with $0<p\le\lambda$. Then there are unique $z_1,z_2\in(0,Z)$ with
--   $$u'(z_1)=\lambda,\qquad u'(z_2)=p, \tag{12}$$
--   and the following is an optimal solution $(x^*,d^*)$ of the prosumer's problem (11):
--
--   1. if $C\le z_2$: $\;x^*=0,\ d^*=[z_1-C]^+$;
--   2. if $C>z_2$: $\;x^*=(C-z_2)\cdot\mathbf 1\{\mathcal X\},\ d^*=0$, where $\mathcal X=\{P\le p(C-z_2)+u(z_2)-u(C)\}$.
--
--   The prosumer sells to the aggregator exactly when her capacity exceeds the consumption level $z_2$ at which marginal utility equals the offered unit price and the fee does not exceed the extra surplus from selling.
--
--   **Formalization Note** The lemma is stated under the standing restriction $p\le\lambda$ of p. 10. The hypothesis $p>0$ is added because $z_2$ exists only then, and $P\ge0$ is added because it is the aggregator's domain (14)–(15) and the first case fails for a negative fee (selling a tiny amount would then be strictly better). "Optimal response" is stated as *an* optimal solution of (11): at the fee threshold, or at $p=\lambda$, other optimal solutions exist.
-- source:
--   Gao, Alshehri, Birge, Aggregating Distributed Energy Resources: Efficiency and Market Power, working paper, SSRN abstract 3931052 (PDF of September 26, 2021), p. 10, Lemma 3, (10)–(12); proof pp. 41–42

import Mathlib
import Definitions.Def_DERAggregation_Unregulated_Setting

namespace DERAggregation.Unregulated

open Set

/-- Lemma 3 (p. 10). Under Assumption 1, for a two-part offer `(P, p)` with `P ≥ 0` and
`0 < p ≤ λ`, the roots `z₁`, `z₂` of `u'(z₁) = λ`, `u'(z₂) = p` in `(0, Z)` exist and are unique,
and the prosumer's problem (11) has the optimal solution: `x* = 0`, `d* = [z₁ − C]⁺` if
`C ≤ z₂`; `x* = (C − z₂)·1{P ≤ p(C − z₂) + u(z₂) − u(C)}`, `d* = 0` if `C > z₂`. -/
theorem lemma_3 (u : ℝ → ℝ) (C Z : ℝ) (hu : UtilAssm u C Z) (lam P p : ℝ) (hP : 0 ≤ P)
    (hp : 0 < p) (hpl : p ≤ lam) :
    (∃! z1, z1 ∈ Ioo 0 Z ∧ deriv u z1 = lam) ∧ (∃! z2, z2 ∈ Ioo 0 Z ∧ deriv u z2 = p) ∧
      ∀ z1 z2 : ℝ, z1 ∈ Ioo 0 Z → deriv u z1 = lam → z2 ∈ Ioo 0 Z → deriv u z2 = p →
        (C ≤ z2 → IsResp u C Z lam P p 0 (max (z1 - C) 0)) ∧
        (z2 < C → IsResp u C Z lam P p
          ((C - z2) * (if P ≤ p * (C - z2) + u z2 - u C then 1 else 0)) 0) := by sorry

end DERAggregation.Unregulated
