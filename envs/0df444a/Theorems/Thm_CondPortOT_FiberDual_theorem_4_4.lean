-- Prove2me | Theorems.Thm_CondPortOT_FiberDual_theorem_4_4
-- name    : CondPortOT.FiberDual.theorem_4_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:35:30.209118+00:00
-- url     : https://prove2.me/theorems/28f6c55d-3de8-4bff-9607-edf752192c43
-- title:
--   Theorem 4.4 — for γ > 0, ε > 0, ρ > ρ_min the worst-case conditional expected loss equals the dual program over 𝒱
-- statement:
--   Let $\mathcal X,\mathcal Y$ be Polish spaces, $(\hat x_i,\hat y_i)_{i\in[N]}$ the samples with $N\ge1$, $x_0\in\mathcal X$, and let Assumption 2.4 and the boundary-regularity predicate hold for the fiber $\mathcal N_\gamma(x_0)$. Suppose $\gamma>0$, $\varepsilon>0$ and $\rho>\rho_{\min}(x_0,\gamma,\varepsilon)$, let $d_i$ be defined as in (14), and let $\ell:\mathcal Y\to\mathbb R$ be a measurable loss (the loss $\ell(\cdot,\alpha,\beta)$ at a feasible portfolio $(\alpha,\beta)$). Then
--   $$\sup_{\substack{\mathbb Q\in\mathbb B_\rho\\ \mathbb Q(X\in\mathcal N_\gamma(x_0))\ge\varepsilon}}\mathbb E_{\mathbb Q}[\ell(Y)\mid X\in\mathcal N_\gamma(x_0)]=\left\{\begin{array}{ll}\inf & \phi+(N\varepsilon)^{-1}\nu^+-N^{-1}\nu^-\\ \text{s.t.} & (\lambda,s,\nu^+,\nu^-,\phi,\varphi,\psi)\in\mathcal V\\ & s_i\ge\sup_{y_i\in\mathcal Y}\{\ell(y_i)-\lambda_i\mathbb D_{\mathcal Y}(y_i,\hat y_i)\}\quad\forall i\in[N].\end{array}\right.$$
--
--   The worst-case conditional expected loss over an optimal transport ball, an infinite-dimensional problem over measures, is thus the value of a finite-dimensional program whose only infinite part is the per-sample supremum over $y_i$. Plugging it into the outer minimization over portfolios gives a tractable robust conditional portfolio problem.
--
--   **Formalization Note.** The loss is any measurable $L:\mathcal Y\to\mathbb R$, standing for $y\mapsto\ell(y,\alpha,\beta)$ at an arbitrary fixed $(\alpha,\beta)$. Both sides are extended reals: the conditional expectation uses $\int\ell^+-\int\ell^-$, the supremum over $y$ may be $+\infty$, and the infimum over an empty set is $+\infty$. Two hypotheses are added to the page: the boundary-regularity predicate (leaving the fiber from $\hat x_i$, $i\in\mathcal I_1$, costs $d_i$ in the limit, and $d_i=\kappa_i$ for $i\in\mathcal I_2$), which the proof uses and which does not follow from Assumption 2.4 for a general continuous cost; and measurability of $L$. $\varepsilon\le1$ is not assumed: for $\varepsilon>1$ the hypothesis $\rho>\rho_{\min}$ fails.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, p. 20, Theorem 4.4 and display (16)

import Mathlib
import Definitions.Def_CondPortOT_FiberDual_Setting
open MeasureTheory RWPI.SqrtLasso ModelRiskOT.Duality

namespace CondPortOT.FiberDual

theorem theorem_4_4 {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (γ : ℝ) (hγ : 0 < γ) (hA : CondPortOT.BigRadius.Assumption24 DX DY x0 γ xh)
    (hH2 : CondPortOT.BigRadius.BoundaryRegular DX x0 γ xh)
    (ε : ℝ) (hε : 0 < ε) (ρ : ℝ) (hρ : CondPortOT.SingDual.rhoMin DX DY xh yh x0 γ ε < ENNReal.ofReal ρ)
    (L : Y → ℝ) (hL : Measurable L) :
    CondPortOT.SingDual.worstCaseGe DX DY xh yh x0 γ ρ ε L =
      ⨅ (v : DualPt N) (_ : InV (CondPortOT.BigRadius.bdDist DX x0 γ xh) (CondPortOT.BigRadius.I1 DX x0 γ xh) ρ v ∧
          ∀ i, (⨆ y, ((L y - v.lam i * DY y (yh i) : ℝ) : EReal)) ≤ (v.s i : EReal)),
        ((v.phi + ((N : ℝ) * ε)⁻¹ * v.nuP - (N : ℝ)⁻¹ * v.nuM : ℝ) : EReal) := by sorry

end CondPortOT.FiberDual
