-- Prove2me | Theorems.Thm_FZEchelon_NormalDemand_kappa_deriv_limit
-- name    : FZEchelon.NormalDemand.kappa_deriv_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:45:05.880728+00:00
-- url     : https://prove2.me/theorems/397ee36d-b2e8-4ece-aaa2-64f0fb8b9b1a
-- title:
--   §4, p. 831 — $\kappa'(x)=-\Phi[\tau_1(x),\tau_2(x);-\sigma^{(L)}/\sigma^{(L+l+1)}]$ and $\lim_{x\to\infty}\kappa(x)=0$
-- statement:
--   Throughout, one-period demand is $u\sim N(\mu,\sigma^2)$ with $\sigma>0$, demands in different periods are independent, $u^{(i)}$ is $i$-period demand with mean $\mu^{(i)}=i\mu$ and standard deviation $\sigma^{(i)}=i^{1/2}\sigma$, density $f^{(i)}$ and cdf $F^{(i)}$. The cost factors $h^d,h^r,p^r$ are positive, $p^s=h^d+p^r$, the shipment lead time is $l\ge 0$ and the order lead time is $L\ge 1$. Costs are average costs ($\alpha=1$), so $R(x)=-h^d(x-\mu^{(l)})+p^rE[u^{(l+1)}-x]^++(h^d+h^r)E[x-u^{(l+1)}]^+$, $x^{r*}$ is a global minimizer of $R$, $P(x)=0$ for $x\ge x^{r*}$ and $P(x)=R(x)-R(x^{r*})$ for $x<x^{r*}$, and $P^L(x)=E\,P[x-u^{(L)}]$. Let $\rho=-\sigma^{(L)}/\sigma^{(L+l+1)}$ and let $\kappa$ be the function defined on p. 830 of the paper.
--
--   Then for every real $x$,
--   $$\kappa'(x)=-\Phi[\tau_1(x),\tau_2(x);\rho],$$
--   and $\kappa(x)\to0$ as $x\to\infty$.
--
--   This integrates the second term of (15) and produces the $-(p^s+h^r)\kappa(x)$ term of (13).
--
--   **Formalization Note** The model data are bundled in the structure `FZEchelon.NormalDemand.Data`. The hypotheses $\sigma>0$ and $L\ge 1$ are added relative to the page: with $\sigma=0$ or $L=0$ some $\sigma^{(i)}$ in a denominator vanishes and Lean's division by zero returns $0$. The paper's §4 also states the normal law violates $u\ge0$ and "ignores this objection"; no nonnegativity of demand is assumed here, and the identity is exact for the normal law. The hypothesis that $x^{r*}$ minimizes $R$ is the paper's property (b) at $\alpha=1$.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 831, paragraph after eq. (15) and 'The last three equations yield the desired result'

import Mathlib
import Definitions.Def_FZEchelon_NormalDemand_Model

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace FZEchelon.NormalDemand

open Data

theorem kappa_deriv_limit (D : Data) (hσ : 0 < D.σ) (hhd : 0 < D.hd) (hhr : 0 < D.hr) (hpr : 0 < D.pr)
    (hL : 1 ≤ D.L) (hx : ∀ x, D.R D.xstar ≤ D.R x) :
    (∀ x : ℝ, HasDerivAt D.kappa
      (-bivNormalCDF (D.tau1 x) (D.tau2 x) D.rho) x) ∧
    Tendsto D.kappa atTop (𝓝 0) := by sorry

end FZEchelon.NormalDemand
