-- Prove2me | Theorems.Thm_FZEchelon_NormalDemand_eq12_PL_integral
-- name    : FZEchelon.NormalDemand.eq12_PL_integral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:44:18.580516+00:00
-- url     : https://prove2.me/theorems/8d4b7df8-ab4d-4fd6-bd07-6cf77cd4422b
-- title:
--   Eq. (12), p. 829 — $P^L(x)=\int_{x-x^{r*}}^\infty[R(x-t)-R(x^{r*})]f^{(L)}(t)\,dt$
-- statement:
--   Throughout, one-period demand is $u\sim N(\mu,\sigma^2)$ with $\sigma>0$, demands in different periods are independent, $u^{(i)}$ is $i$-period demand with mean $\mu^{(i)}=i\mu$ and standard deviation $\sigma^{(i)}=i^{1/2}\sigma$, density $f^{(i)}$ and cdf $F^{(i)}$. The cost factors $h^d,h^r,p^r$ are positive, $p^s=h^d+p^r$, the shipment lead time is $l\ge 0$ and the order lead time is $L\ge 1$. Costs are average costs ($\alpha=1$), so $R(x)=-h^d(x-\mu^{(l)})+p^rE[u^{(l+1)}-x]^++(h^d+h^r)E[x-u^{(l+1)}]^+$, $x^{r*}$ is a global minimizer of $R$, $P(x)=0$ for $x\ge x^{r*}$ and $P(x)=R(x)-R(x^{r*})$ for $x<x^{r*}$, and $P^L(x)=E\,P[x-u^{(L)}]$.
--
--   Then for every real $x$,
--   $$P^L(x)=\int_{x-x^{r*}}^{\infty}[R(x-t)-R(x^{r*})]\,f^{(L)}(t)\,dt .$$
--
--   This expresses the expected induced penalty as a single integral against the density of $L$-period demand, the starting point of the closed-form computation.
--
--   **Formalization Note** The model data are bundled in the structure `FZEchelon.NormalDemand.Data`. The hypotheses $\sigma>0$ and $L\ge 1$ are added relative to the page: with $\sigma=0$ or $L=0$ some $\sigma^{(i)}$ in a denominator vanishes and Lean's division by zero returns $0$. The paper's §4 also states the normal law violates $u\ge0$ and "ignores this objection"; no nonnegativity of demand is assumed here, and the identity is exact for the normal law. The hypothesis that $x^{r*}$ minimizes $R$ is the paper's property (b) at $\alpha=1$.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 829, eq. (12)

import Mathlib
import Definitions.Def_FZEchelon_NormalDemand_Model

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace FZEchelon.NormalDemand

open Data

theorem eq12_PL_integral (D : Data) (hσ : 0 < D.σ) (hhd : 0 < D.hd) (hhr : 0 < D.hr) (hpr : 0 < D.pr)
    (hL : 1 ≤ D.L) (hx : ∀ x, D.R D.xstar ≤ D.R x) :
    ∀ x : ℝ, D.PL x = ∫ t in Set.Ioi (x - D.xstar), (D.R (x - t) - D.R D.xstar) * D.f D.L t := by sorry

end FZEchelon.NormalDemand
