-- Prove2me | Theorems.Thm_FZEchelon_NormalDemand_eq11_R_formula
-- name    : FZEchelon.NormalDemand.eq11_R_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:44:14.836093+00:00
-- url     : https://prove2.me/theorems/35cdb789-04b2-458a-9733-0970bc9363c1
-- title:
--   Eq. (11), p. 829 — $R(x)=p^s[\mu^{(l+1)}-x]+(p^s+h^r)\int_{-\infty}^xF^{(l+1)}(t)\,dt-h^d\mu$
-- statement:
--   Throughout, one-period demand is $u\sim N(\mu,\sigma^2)$ with $\sigma>0$, demands in different periods are independent, $u^{(i)}$ is $i$-period demand with mean $\mu^{(i)}=i\mu$ and standard deviation $\sigma^{(i)}=i^{1/2}\sigma$, density $f^{(i)}$ and cdf $F^{(i)}$. The cost factors $h^d,h^r,p^r$ are positive, $p^s=h^d+p^r$, the shipment lead time is $l\ge 0$ and the order lead time is $L\ge 1$. Costs are average costs ($\alpha=1$), so $R(x)=-h^d(x-\mu^{(l)})+p^rE[u^{(l+1)}-x]^++(h^d+h^r)E[x-u^{(l+1)}]^+$, $x^{r*}$ is a global minimizer of $R$, $P(x)=0$ for $x\ge x^{r*}$ and $P(x)=R(x)-R(x^{r*})$ for $x<x^{r*}$, and $P^L(x)=E\,P[x-u^{(L)}]$.
--
--   Then for every real $x$,
--   $$R(x)=p^s[\mu^{(l+1)}-x]+(p^s+h^r)\int_{-\infty}^{x}F^{(l+1)}(t)\,dt-h^d\mu .$$
--
--   This rewrites the expected-cost definition of $R$ in terms of the integrated cdf of $(l+1)$-period demand; it is the form used to differentiate $R$ in (14).
--
--   **Formalization Note** The model data are bundled in the structure `FZEchelon.NormalDemand.Data`. The hypotheses $\sigma>0$ and $L\ge 1$ are added relative to the page: with $\sigma=0$ or $L=0$ some $\sigma^{(i)}$ in a denominator vanishes and Lean's division by zero returns $0$. The paper's §4 also states the normal law violates $u\ge0$ and "ignores this objection"; no nonnegativity of demand is assumed here, and the identity is exact for the normal law. The hypothesis that $x^{r*}$ minimizes $R$ is the paper's property (b) at $\alpha=1$.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 829, eq. (11)

import Mathlib
import Definitions.Def_FZEchelon_NormalDemand_Model

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace FZEchelon.NormalDemand

open Data

theorem eq11_R_formula (D : Data) (hσ : 0 < D.σ) (hhd : 0 < D.hd) (hhr : 0 < D.hr) (hpr : 0 < D.pr)
    (hL : 1 ≤ D.L) (hx : ∀ x, D.R D.xstar ≤ D.R x) :
    ∀ x : ℝ, D.R x = D.ps * (D.mean (D.l + 1) - x)
      + (D.ps + D.hr) * (∫ t in Set.Iic x, D.F (D.l + 1) t) - D.hd * D.μ := by sorry

end FZEchelon.NormalDemand
