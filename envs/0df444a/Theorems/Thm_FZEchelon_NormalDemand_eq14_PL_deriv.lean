-- Prove2me | Theorems.Thm_FZEchelon_NormalDemand_eq14_PL_deriv
-- name    : FZEchelon.NormalDemand.eq14_PL_deriv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:44:16.917034+00:00
-- url     : https://prove2.me/theorems/4ba569c2-5b38-4ed4-88b0-cc06c97972c0
-- title:
--   Eq. (14), p. 830 — $P^{L\prime}(x)=-p^s\Phi[\tau_1(x)]+(p^s+h^r)\int_{x-x^{r*}}^\infty F^{(l+1)}(x-t)f^{(L)}(t)\,dt$
-- statement:
--   Throughout, one-period demand is $u\sim N(\mu,\sigma^2)$ with $\sigma>0$, demands in different periods are independent, $u^{(i)}$ is $i$-period demand with mean $\mu^{(i)}=i\mu$ and standard deviation $\sigma^{(i)}=i^{1/2}\sigma$, density $f^{(i)}$ and cdf $F^{(i)}$. The cost factors $h^d,h^r,p^r$ are positive, $p^s=h^d+p^r$, the shipment lead time is $l\ge 0$ and the order lead time is $L\ge 1$. Costs are average costs ($\alpha=1$), so $R(x)=-h^d(x-\mu^{(l)})+p^rE[u^{(l+1)}-x]^++(h^d+h^r)E[x-u^{(l+1)}]^+$, $x^{r*}$ is a global minimizer of $R$, $P(x)=0$ for $x\ge x^{r*}$ and $P(x)=R(x)-R(x^{r*})$ for $x<x^{r*}$, and $P^L(x)=E\,P[x-u^{(L)}]$. $\Phi$ is the standard normal cdf and $\tau_1(x)=-[x-(x^{r*}+\mu^{(L)})]/\sigma^{(L)}$.
--
--   Then $R$ is differentiable on $\mathbb R$, and for every real $x$ the function $P^L$ is differentiable at $x$ with
--   $$P^{L\prime}(x)=\int_{x-x^{r*}}^{\infty}R'(x-t)f^{(L)}(t)\,dt=-p^s\Phi[\tau_1(x)]+(p^s+h^r)\int_{x-x^{r*}}^{\infty}F^{(l+1)}(x-t)f^{(L)}(t)\,dt .$$
--
--   This is the first step of the derivation of (13): differentiation under the integral in (12), followed by (11).
--
--   **Formalization Note** The model data are bundled in the structure `FZEchelon.NormalDemand.Data`. The hypotheses $\sigma>0$ and $L\ge 1$ are added relative to the page: with $\sigma=0$ or $L=0$ some $\sigma^{(i)}$ in a denominator vanishes and Lean's division by zero returns $0$. The paper's §4 also states the normal law violates $u\ge0$ and "ignores this objection"; no nonnegativity of demand is assumed here, and the identity is exact for the normal law. The hypothesis that $x^{r*}$ minimizes $R$ is the paper's property (b) at $\alpha=1$.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 830, eq. (14)

import Mathlib
import Definitions.Def_FZEchelon_NormalDemand_Model

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace FZEchelon.NormalDemand

open Data

theorem eq14_PL_deriv (D : Data) (hσ : 0 < D.σ) (hhd : 0 < D.hd) (hhr : 0 < D.hr) (hpr : 0 < D.pr)
    (hL : 1 ≤ D.L) (hx : ∀ x, D.R D.xstar ≤ D.R x) :
    Differentiable ℝ D.R ∧
    ∀ x : ℝ,
      HasDerivAt D.PL (∫ t in Set.Ioi (x - D.xstar), deriv D.R (x - t) * D.f D.L t) x ∧
      (∫ t in Set.Ioi (x - D.xstar), deriv D.R (x - t) * D.f D.L t)
        = -D.ps * stdNormalCDF (D.tau1 x)
          + (D.ps + D.hr) * ∫ t in Set.Ioi (x - D.xstar), D.F (D.l + 1) (x - t) * D.f D.L t := by sorry

end FZEchelon.NormalDemand
