-- Prove2me | Theorems.Thm_FZEchelon_NormalDemand_eq15_PL_deriv_bivariate
-- name    : FZEchelon.NormalDemand.eq15_PL_deriv_bivariate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:44:28.81582+00:00
-- url     : https://prove2.me/theorems/8232ff12-e933-436b-a793-a7cbb0553e15
-- title:
--   Eq. (15), p. 831 — $P^{L\prime}(x)=-p^s\Phi[\tau_1(x)]+(p^s+h^r)\Phi[\tau_1(x),\tau_2(x);-\sigma^{(L)}/\sigma^{(L+l+1)}]$
-- statement:
--   Throughout, one-period demand is $u\sim N(\mu,\sigma^2)$ with $\sigma>0$, demands in different periods are independent, $u^{(i)}$ is $i$-period demand with mean $\mu^{(i)}=i\mu$ and standard deviation $\sigma^{(i)}=i^{1/2}\sigma$, density $f^{(i)}$ and cdf $F^{(i)}$. The cost factors $h^d,h^r,p^r$ are positive, $p^s=h^d+p^r$, the shipment lead time is $l\ge 0$ and the order lead time is $L\ge 1$. Costs are average costs ($\alpha=1$), so $R(x)=-h^d(x-\mu^{(l)})+p^rE[u^{(l+1)}-x]^++(h^d+h^r)E[x-u^{(l+1)}]^+$, $x^{r*}$ is a global minimizer of $R$, $P(x)=0$ for $x\ge x^{r*}$ and $P(x)=R(x)-R(x^{r*})$ for $x<x^{r*}$, and $P^L(x)=E\,P[x-u^{(L)}]$. $\Phi$ is the standard normal cdf, $\Phi(\xi_1,\xi_2;\rho)$ is the bivariate standard normal cdf with correlation $\rho$, $\tau_1(x)=-[x-(x^{r*}+\mu^{(L)})]/\sigma^{(L)}$ and $\tau_2(x)=[x-\mu^{(L+l+1)}]/\sigma^{(L+l+1)}$.
--
--   Then for every real $x$, $P^L$ is differentiable at $x$ with
--   $$P^{L\prime}(x)=-p^s\Phi[\tau_1(x)]+(p^s+h^r)\,\Phi\big[\tau_1(x),\tau_2(x);-\sigma^{(L)}/\sigma^{(L+l+1)}\big].$$
--
--   The integral in (14) is the probability $\Pr\{u^{(L)}\ge x-x^{r*},\,u^{(L)}+u^{(l+1)}\le x\}$, and (15) writes it in standardized bivariate normal form.
--
--   **Formalization Note** The model data are bundled in the structure `FZEchelon.NormalDemand.Data`. The hypotheses $\sigma>0$ and $L\ge 1$ are added relative to the page: with $\sigma=0$ or $L=0$ some $\sigma^{(i)}$ in a denominator vanishes and Lean's division by zero returns $0$. The paper's §4 also states the normal law violates $u\ge0$ and "ignores this objection"; no nonnegativity of demand is assumed here, and the identity is exact for the normal law. The hypothesis that $x^{r*}$ minimizes $R$ is the paper's property (b) at $\alpha=1$.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 831, eq. (15)

import Mathlib
import Definitions.Def_FZEchelon_NormalDemand_Model

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace FZEchelon.NormalDemand

open Data

theorem eq15_PL_deriv_bivariate (D : Data) (hσ : 0 < D.σ) (hhd : 0 < D.hd) (hhr : 0 < D.hr) (hpr : 0 < D.pr)
    (hL : 1 ≤ D.L) (hx : ∀ x, D.R D.xstar ≤ D.R x) :
    ∀ x : ℝ, HasDerivAt D.PL
      (-D.ps * stdNormalCDF (D.tau1 x)
        + (D.ps + D.hr) * bivNormalCDF (D.tau1 x) (D.tau2 x) D.rho) x := by sorry

end FZEchelon.NormalDemand
