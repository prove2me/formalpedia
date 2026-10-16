-- Prove2me | Theorems.Thm_CondPortOT_SingUninf_proposition_3_1
-- name    : CondPortOT.SingUninf.proposition_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:20.074357+00:00
-- url     : https://prove2.me/theorems/bc2e8a35-3ed1-4952-b0cb-a711ddd8fdd3
-- title:
--   Proposition 3.1 — for ε = γ = 0 and ρ > 0 the worst-case conditional expected loss equals sup_{y∈𝒴} ℓ(y)
-- statement:
--   Let $\mathcal X$ (covariates) and $\mathcal Y$ (returns) be Polish spaces with Borel $\sigma$-algebras, let $(\widehat x_i,\widehat y_i)$, $i\in[N]$, $N\ge1$, be the data with empirical measure $\widehat{\mathbb P}$, let $x_0\in\mathcal X$, and let $\mathbb B_\rho$ be the optimal transport ball of radius $\rho$ around $\widehat{\mathbb P}$ for the ground cost $\mathbb D_{\mathcal X}+\mathbb D_{\mathcal Y}$. Suppose Assumption 2.4 holds with fiber radius $\gamma=0$ and that $x_0$ is not isolated for $\mathbb D_{\mathcal X}$. Then for every $\rho>0$ and every loss $\ell:\mathcal Y\to\mathbb R$,
--
--   $$\sup_{\mathbb Q\in\mathbb B_\rho,\ \mathbb Q(X=x_0)>0}\mathbb E_{\mathbb Q}[\ell(Y)\mid X=x_0]=\sup_{y\in\mathcal Y}\ell(y),$$
--
--   with both sides in $[-\infty,+\infty]$.
--
--   This is the case $\varepsilon=\gamma=0$ of the robustified conditional portfolio problem (4), with the mass constraint taken as the strict inequality $\mathbb Q(X=x_0)>0$. The result is negative: the worst-case conditional loss does not depend on the data and equals the robust (support-function) value, so conditioning on a single covariate value with an optimal transport ball is uninformative.
--
--   **Formalization Note** $\ell$ stands for $y\mapsto\ell(y,\alpha,\beta)$ at an arbitrary fixed decision $(\alpha,\beta)$, so the theorem quantifies over all functions $\ell:\mathcal Y\to\mathbb R$; no measurability, boundedness or integrability is assumed, and the conditional expectation uses the extended integral. "$X=x_0$" is the fiber $\{x:\mathbb D_{\mathcal X}(x,x_0)\le0\}\times\mathcal Y$, equal to $\{x_0\}\times\mathcal Y$ under Assumption 2.4(i). The hypothesis that $x_0$ is not isolated (for every $r>0$ some $x\ne x_0$ has $\mathbb D_{\mathcal X}(x,x_0)\le r$) is an addition to the paper: it is Assumption 2.4(iii) at $\gamma=0$ when the boundary of $\{x_0\}$ is taken in an ambient Euclidean space, as the paper's remark on p. 11 suggests, and the proof uses it; with the boundary taken in $\mathcal X$ itself, Assumption 2.4(iii) is vacuous at an isolated point, where the statement fails.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, p. 14, Proposition 3.1 (setting: §3.1, p. 14)

import Mathlib
import Definitions.Def_CondPortOT_SingUninf_Setting

open MeasureTheory

namespace CondPortOT.SingUninf

theorem proposition_3_1 {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (hA : Assumption24 DX DY x0 0 xh) (hH1 : NotIsolated DX x0)
    (ρ : ℝ) (hρ : 0 < ρ) (L : Y → ℝ) :
    worstCasePos DX DY xh yh x0 0 ρ L = ⨆ y, (L y : EReal) := by sorry

end CondPortOT.SingUninf
