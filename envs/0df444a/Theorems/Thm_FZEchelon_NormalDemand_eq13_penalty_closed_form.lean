-- Prove2me | Theorems.Thm_FZEchelon_NormalDemand_eq13_penalty_closed_form
-- name    : FZEchelon.NormalDemand.eq13_penalty_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T11:45:28.099874+00:00
-- url     : https://prove2.me/theorems/460adb78-2d9a-48e9-9188-8bb3426f1ad4
-- title:
--   Eq. (13), p. 830 — closed form $P^L(x)=p^s\iota(x)-(p^s+h^r)\kappa(x)$ of the induced penalty cost under normal demand
-- statement:
--   Throughout, one-period demand is $u\sim N(\mu,\sigma^2)$ with $\sigma>0$, demands in different periods are independent, $u^{(i)}$ is $i$-period demand with mean $\mu^{(i)}=i\mu$ and standard deviation $\sigma^{(i)}=i^{1/2}\sigma$, density $f^{(i)}$ and cdf $F^{(i)}$. The cost factors $h^d,h^r,p^r$ are positive, $p^s=h^d+p^r$, the shipment lead time is $l\ge 0$ and the order lead time is $L\ge 1$. Costs are average costs ($\alpha=1$), so $R(x)=-h^d(x-\mu^{(l)})+p^rE[u^{(l+1)}-x]^++(h^d+h^r)E[x-u^{(l+1)}]^+$, $x^{r*}$ is a global minimizer of $R$, $P(x)=0$ for $x\ge x^{r*}$ and $P(x)=R(x)-R(x^{r*})$ for $x<x^{r*}$, and $P^L(x)=E\,P[x-u^{(L)}]$. Let $\Phi,\phi$ be the standard normal cdf and density, $\Phi(\xi_1,\xi_2;\rho)$ the bivariate standard normal cdf with correlation $\rho$, $\Theta(z)=z\Phi(z)+\phi(z)$, and
--   $$\tau_1(x)=-\frac{x-(x^{r*}+\mu^{(L)})}{\sigma^{(L)}},\quad \tau_2(x)=\frac{x-\mu^{(L+l+1)}}{\sigma^{(L+l+1)}},\quad \nu^{r*}=\frac{x^{r*}-\mu^{(l+1)}}{\sigma^{(l+1)}},$$
--   $$\tau_3(x)=-\frac{x-(x^{r*}+\mu^{(L)})-[\sigma^{(L)}/\sigma^{(l+1)}]^2[x^{r*}-\mu^{(l+1)}]}{\sigma^{(L)}\sigma^{(L+l+1)}/\sigma^{(l+1)}},$$
--   $$\epsilon_1(x)=\Phi[\tau_3(x)]\phi[\tau_2(x)]/\sigma^{(L+l+1)},\qquad \epsilon_2(x)=\Phi(\nu^{r*})\phi[\tau_1(x)]/\sigma^{(L)},$$
--   $$\iota(x)=\sigma^{(L)}\Theta[\tau_1(x)],$$
--   $$\kappa(x)=\sigma^{(l+1)}\Theta(\nu^{r*})\Phi[\tau_1(x)]-\{[\sigma^{(L+l+1)}]^2\epsilon_1(x)-[\sigma^{(L)}]^2\epsilon_2(x)\}-[x-\mu^{(L+l+1)}]\,\Phi\big[\tau_1(x),\tau_2(x);-\sigma^{(L)}/\sigma^{(L+l+1)}\big].$$
--
--   Then for every real $x$,
--   $$P^L(x)=p^s\iota(x)-(p^s+h^r)\kappa(x).$$
--
--   The expected induced penalty cost $P^L$ is the only nonlinear part of the one-period cost of the single-location problem to which the paper reduces the two-echelon system. Under normal demand it needs no numerical integration: it is a closed form in the univariate and bivariate standard normal cdfs.
--
--   **Formalization Note** The model data are bundled in the structure `FZEchelon.NormalDemand.Data`. The hypotheses $\sigma>0$ and $L\ge 1$ are added relative to the page: with $\sigma=0$ or $L=0$ some $\sigma^{(i)}$ in a denominator vanishes and Lean's division by zero returns $0$. The paper's §4 also states the normal law violates $u\ge0$ and "ignores this objection"; no nonnegativity of demand is assumed here, and the identity is exact for the normal law. The hypothesis that $x^{r*}$ minimizes $R$ is the paper's property (b) at $\alpha=1$.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 830, eq. (13) with the definitions of τ1, τ2, τ3, ν^{r*}, ε1, ε2, Θ, ι, κ

import Mathlib
import Definitions.Def_FZEchelon_NormalDemand_Model

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace FZEchelon.NormalDemand

open Data

theorem eq13_penalty_closed_form (D : Data) (hσ : 0 < D.σ) (hhd : 0 < D.hd) (hhr : 0 < D.hr) (hpr : 0 < D.pr)
    (hL : 1 ≤ D.L) (hx : ∀ x, D.R D.xstar ≤ D.R x) :
    ∀ x : ℝ, D.PL x = D.ps * D.iota x - (D.ps + D.hr) * D.kappa x := by sorry

end FZEchelon.NormalDemand
