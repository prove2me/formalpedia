-- Prove2me | Theorems.Thm_FZEchelon_NormalDemand_conditional_normal_identities
-- name    : FZEchelon.NormalDemand.conditional_normal_identities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:44:41.858641+00:00
-- url     : https://prove2.me/theorems/1e0b0309-4f08-4131-9514-ca383aaf94c9
-- title:
--   §4, p. 831 — the conditional-normal identities $P\{\zeta_1\le\tau_1\mid\zeta_2=\tau_2\}=\Phi[\tau_3]$ and $P\{\zeta_2\le\tau_2\mid\zeta_1=\tau_1\}=\Phi(\nu^{r*})$, in density form
-- statement:
--   Throughout, one-period demand is $u\sim N(\mu,\sigma^2)$ with $\sigma>0$, demands in different periods are independent, $u^{(i)}$ is $i$-period demand with mean $\mu^{(i)}=i\mu$ and standard deviation $\sigma^{(i)}=i^{1/2}\sigma$, density $f^{(i)}$ and cdf $F^{(i)}$. The cost factors $h^d,h^r,p^r$ are positive, $p^s=h^d+p^r$, the shipment lead time is $l\ge 0$ and the order lead time is $L\ge 1$. Costs are average costs ($\alpha=1$), so $R(x)=-h^d(x-\mu^{(l)})+p^rE[u^{(l+1)}-x]^++(h^d+h^r)E[x-u^{(l+1)}]^+$, $x^{r*}$ is a global minimizer of $R$, $P(x)=0$ for $x\ge x^{r*}$ and $P(x)=R(x)-R(x^{r*})$ for $x<x^{r*}$, and $P^L(x)=E\,P[x-u^{(L)}]$. Let $\rho=-\sigma^{(L)}/\sigma^{(L+l+1)}$, let $\phi_2(s,t;\rho)$ be the bivariate standard normal density with correlation $\rho$, and let $\tau_1,\tau_2,\tau_3,\nu^{r*}$ be as on p. 830 of the paper.
--
--   Then for every real $x$,
--   $$\int_{-\infty}^{\tau_1(x)}\phi_2(s,\tau_2(x);\rho)\,ds=\Phi[\tau_3(x)]\,\phi[\tau_2(x)],\qquad \int_{-\infty}^{\tau_2(x)}\phi_2(\tau_1(x),t;\rho)\,dt=\Phi(\nu^{r*})\,\phi[\tau_1(x)].$$
--
--   For a standardized pair $(\zeta_1,\zeta_2)$ with density $\phi_2(\cdot,\cdot;\rho)$, the left sides are $P\{\zeta_1\le\tau_1(x)\mid\zeta_2=\tau_2(x)\}\,\phi[\tau_2(x)]$ and $P\{\zeta_2\le\tau_2(x)\mid\zeta_1=\tau_1(x)\}\,\phi[\tau_1(x)]$, so the two identities are the paper's statements $P\{\zeta_1\le\tau_1(x)\mid\zeta_2=\tau_2(x)\}=\Phi[\tau_3(x)]$ and $P\{\zeta_2\le\tau_2(x)\mid\zeta_1=\tau_1(x)\}=\Phi(\nu^{r*})$. They give the partial derivatives of the bivariate cdf along the curve $x\mapsto(\tau_1(x),\tau_2(x))$.
--
--   **Formalization Note** The model data are bundled in the structure `FZEchelon.NormalDemand.Data`. The hypotheses $\sigma>0$ and $L\ge 1$ are added relative to the page: with $\sigma=0$ or $L=0$ some $\sigma^{(i)}$ in a denominator vanishes and Lean's division by zero returns $0$. The paper's §4 also states the normal law violates $u\ge0$ and "ignores this objection"; no nonnegativity of demand is assumed here, and the identity is exact for the normal law. The hypothesis that $x^{r*}$ minimizes $R$ is the paper's property (b) at $\alpha=1$. The conditional probabilities given the null events $\{\zeta_2=\tau_2(x)\}$ and $\{\zeta_1=\tau_1(x)\}$ are stated in this density form, because a conditional probability given a null event is not defined pointwise.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 831, displays after 'This fact and tedious algebra can be used to show'

import Mathlib
import Definitions.Def_FZEchelon_NormalDemand_Model

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace FZEchelon.NormalDemand

open Data

theorem conditional_normal_identities (D : Data) (hσ : 0 < D.σ) (hhd : 0 < D.hd) (hhr : 0 < D.hr) (hpr : 0 < D.pr)
    (hL : 1 ≤ D.L) (hx : ∀ x, D.R D.xstar ≤ D.R x) :
    ∀ x : ℝ,
      (∫ s in Set.Iic (D.tau1 x), bivNormalPDF D.rho s (D.tau2 x))
          = stdNormalCDF (D.tau3 x) * stdNormalPDF (D.tau2 x) ∧
      (∫ t in Set.Iic (D.tau2 x), bivNormalPDF D.rho (D.tau1 x) t)
          = stdNormalCDF D.nustar * stdNormalPDF (D.tau1 x) := by sorry

end FZEchelon.NormalDemand
