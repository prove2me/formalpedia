-- Prove2me | Theorems.Thm_FZEchelon_NormalDemand_Phi2_comp_deriv
-- name    : FZEchelon.NormalDemand.Phi2_comp_deriv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:44:54.628125+00:00
-- url     : https://prove2.me/theorems/36e50389-5684-4582-acba-94e64e7aa1af
-- title:
--   §4, p. 831 — $(d/dx)\Phi[\tau_1(x),\tau_2(x);-\sigma^{(L)}/\sigma^{(L+l+1)}]=\epsilon_1(x)-\epsilon_2(x)$
-- statement:
--   Throughout, one-period demand is $u\sim N(\mu,\sigma^2)$ with $\sigma>0$, demands in different periods are independent, $u^{(i)}$ is $i$-period demand with mean $\mu^{(i)}=i\mu$ and standard deviation $\sigma^{(i)}=i^{1/2}\sigma$, density $f^{(i)}$ and cdf $F^{(i)}$. The cost factors $h^d,h^r,p^r$ are positive, $p^s=h^d+p^r$, the shipment lead time is $l\ge 0$ and the order lead time is $L\ge 1$. Costs are average costs ($\alpha=1$), so $R(x)=-h^d(x-\mu^{(l)})+p^rE[u^{(l+1)}-x]^++(h^d+h^r)E[x-u^{(l+1)}]^+$, $x^{r*}$ is a global minimizer of $R$, $P(x)=0$ for $x\ge x^{r*}$ and $P(x)=R(x)-R(x^{r*})$ for $x<x^{r*}$, and $P^L(x)=E\,P[x-u^{(L)}]$. Let $\rho=-\sigma^{(L)}/\sigma^{(L+l+1)}$, $\Phi(\xi_1,\xi_2;\rho)$ the bivariate standard normal cdf, and $\tau_1,\tau_2,\epsilon_1,\epsilon_2$ as on p. 830 of the paper.
--
--   Then for every real $x$,
--   $$\frac{d}{dx}\Phi[\tau_1(x),\tau_2(x);\rho]=\epsilon_1(x)-\epsilon_2(x).$$
--
--   This is the chain-rule step that turns the conditional-normal identities into a derivative, used to verify $\kappa'$.
--
--   **Formalization Note** The model data are bundled in the structure `FZEchelon.NormalDemand.Data`. The hypotheses $\sigma>0$ and $L\ge 1$ are added relative to the page: with $\sigma=0$ or $L=0$ some $\sigma^{(i)}$ in a denominator vanishes and Lean's division by zero returns $0$. The paper's §4 also states the normal law violates $u\ge0$ and "ignores this objection"; no nonnegativity of demand is assumed here, and the identity is exact for the normal law. The hypothesis that $x^{r*}$ minimizes $R$ is the paper's property (b) at $\alpha=1$.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 831, display after 'and, therefore,'

import Mathlib
import Definitions.Def_FZEchelon_NormalDemand_Model

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace FZEchelon.NormalDemand

open Data

theorem Phi2_comp_deriv (D : Data) (hσ : 0 < D.σ) (hhd : 0 < D.hd) (hhr : 0 < D.hr) (hpr : 0 < D.pr)
    (hL : 1 ≤ D.L) (hx : ∀ x, D.R D.xstar ≤ D.R x) :
    ∀ x : ℝ, HasDerivAt (fun y => bivNormalCDF (D.tau1 y) (D.tau2 y) D.rho)
      (D.eps1 x - D.eps2 x) x := by sorry

end FZEchelon.NormalDemand
