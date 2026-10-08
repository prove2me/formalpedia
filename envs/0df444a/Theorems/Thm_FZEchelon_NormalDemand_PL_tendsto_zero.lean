-- Prove2me | Theorems.Thm_FZEchelon_NormalDemand_PL_tendsto_zero
-- name    : FZEchelon.NormalDemand.PL_tendsto_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:44:42.657531+00:00
-- url     : https://prove2.me/theorems/aa798271-c294-4e87-b66f-3a3708c939dc
-- title:
--   §4, p. 831 — $\lim_{x\to\infty}P^L(x)=0$, hence $P^L(x)=-\int_x^\infty P^{L\prime}(t)\,dt$
-- statement:
--   Throughout, one-period demand is $u\sim N(\mu,\sigma^2)$ with $\sigma>0$, demands in different periods are independent, $u^{(i)}$ is $i$-period demand with mean $\mu^{(i)}=i\mu$ and standard deviation $\sigma^{(i)}=i^{1/2}\sigma$, density $f^{(i)}$ and cdf $F^{(i)}$. The cost factors $h^d,h^r,p^r$ are positive, $p^s=h^d+p^r$, the shipment lead time is $l\ge 0$ and the order lead time is $L\ge 1$. Costs are average costs ($\alpha=1$), so $R(x)=-h^d(x-\mu^{(l)})+p^rE[u^{(l+1)}-x]^++(h^d+h^r)E[x-u^{(l+1)}]^+$, $x^{r*}$ is a global minimizer of $R$, $P(x)=0$ for $x\ge x^{r*}$ and $P(x)=R(x)-R(x^{r*})$ for $x<x^{r*}$, and $P^L(x)=E\,P[x-u^{(L)}]$.
--
--   Then $P^L(x)\to0$ as $x\to\infty$, and for every real $x$,
--   $$P^L(x)=-\int_x^\infty P^{L\prime}(t)\,dt .$$
--
--   This reduces (13) to integrating the two terms of the derivative (15) from $x$ to $\infty$.
--
--   **Formalization Note** The model data are bundled in the structure `FZEchelon.NormalDemand.Data`. The hypotheses $\sigma>0$ and $L\ge 1$ are added relative to the page: with $\sigma=0$ or $L=0$ some $\sigma^{(i)}$ in a denominator vanishes and Lean's division by zero returns $0$. The paper's §4 also states the normal law violates $u\ge0$ and "ignores this objection"; no nonnegativity of demand is assumed here, and the identity is exact for the normal law. The hypothesis that $x^{r*}$ minimizes $R$ is the paper's property (b) at $\alpha=1$. $P^{L\prime}$ is written `deriv PL`; differentiability of $P^L$ everywhere is the content of (14).
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 831, sentence after eq. (15)

import Mathlib
import Definitions.Def_FZEchelon_NormalDemand_Model

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace FZEchelon.NormalDemand

open Data

theorem PL_tendsto_zero (D : Data) (hσ : 0 < D.σ) (hhd : 0 < D.hd) (hhr : 0 < D.hr) (hpr : 0 < D.pr)
    (hL : 1 ≤ D.L) (hx : ∀ x, D.R D.xstar ≤ D.R x) :
    Tendsto D.PL atTop (𝓝 0) ∧
    ∀ x : ℝ, D.PL x = -∫ t in Set.Ioi x, deriv D.PL t := by sorry

end FZEchelon.NormalDemand
