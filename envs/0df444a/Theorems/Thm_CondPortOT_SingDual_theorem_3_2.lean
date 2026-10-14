-- Prove2me | Theorems.Thm_CondPortOT_SingDual_theorem_3_2
-- name    : CondPortOT.SingDual.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:54.521775+00:00
-- url     : https://prove2.me/theorems/70ca2843-33b8-4d97-b876-60a087996166
-- title:
--   Theorem 3.2, p. 15 — for γ = 0, ε ∈ (0,1], ρ > ρ_min the worst-case conditional expected loss equals a dual over (λ₁, λ₂)
-- statement:
--   Let $\mathcal X,\mathcal Y$ be Polish spaces, $(\hat x_i,\hat y_i)_{i\in[N]}$ with $N\ge1$ samples, and $x_0\in\mathcal X$. Assume Assumption 2.4 with $\gamma=0$, so the fiber is $\{x_0\}\times\mathcal Y$, and that $x_0$ is not isolated for $\mathbb D_{\mathcal X}$. Suppose that $\varepsilon\in(0,1]$ and $\rho>\rho_{\min}(x_0,0,\varepsilon)$. For any feasible solution $(\alpha,\beta)$, writing $\ell(y)=\ell(y,\alpha,\beta)$ (assumed measurable),
--   $$\sup_{\mathbb Q\in\mathbb B_\rho,\ \mathbb Q(X=x_0)\ge\varepsilon}\mathbb E_{\mathbb Q}[\ell(Y)\mid X=x_0]
--   =\inf_{\lambda_1\in\mathbb R_+,\ \lambda_2\in\mathbb R}\Big\{\rho\lambda_1+\varepsilon\lambda_2+\frac1N\sum_{i\in[N]}\Big(\sup_{y_i\in\mathcal Y}\big\{\varepsilon^{-1}\ell(y_i)-[\mathbb D_{\mathcal X}(x_0,\hat x_i)+\mathbb D_{\mathcal Y}(y_i,\hat y_i)]\lambda_1-\lambda_2\big\}\Big)^+\Big\}.$$
--
--   The theorem turns the worst-case conditional expectation over an optimal-transport ball, whose objective is a ratio of two linear functionals of $\mathbb Q$, into a minimisation over two scalar multipliers with $N$ one-dimensional suprema. It is the basis of the conic reformulations of Section 3 for the γ = 0 robust portfolio models.
--
--   **Formalization Note** The loss is any measurable `L : Y → ℝ`, standing for $\ell(\cdot,\alpha,\beta)$ at an arbitrary feasible $(\alpha,\beta)$; no boundedness or continuity is assumed. Both sides are in $[-\infty,\infty]$; the inner suprema may be $+\infty$, in which case the corresponding term is $+\infty$. Conditional expectations are only taken at measures with fiber mass $\ge\varepsilon>0$, and expectations of $\ell$ are $\int\ell^+-\int\ell^-$ (never a Bochner integral). Two hypotheses are added to the page: measurability of $\ell$, and that $x_0$ is not isolated ($\forall r>0\ \exists x\neq x_0$ with $\mathbb D_{\mathcal X}(x,x_0)\le r$) — the paper's Assumption 2.4(iii) at $\gamma=0$ read with the ambient boundary $\partial\{x_0\}=\{x_0\}$, as the paper's remark on p. 11 does. With $\partial$ the frontier in $\mathcal X$, (iii) is vacuous at an isolated $x_0$, and the statement is then false. The hypothesis $\rho>\rho_{\min}$ forces $\rho>0$. Samples are indexed by `Fin N`.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, p. 15, Theorem 3.2; proof pp. 41–42

import Mathlib
import Definitions.Def_CondPortOT_SingDual_Setting

open MeasureTheory

namespace CondPortOT.SingDual

theorem theorem_3_2 {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (hA : Assumption24 DX DY x0 0 xh) (hH1 : CondPortOT.SingUninf.NotIsolated DX x0)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (ρ : ℝ) (hρ : rhoMin DX DY xh yh x0 0 ε < ENNReal.ofReal ρ)
    (L : Y → ℝ) (hL : Measurable L) :
    worstCaseGe DX DY xh yh x0 0 ρ ε L =
      ⨅ (l1 : ℝ) (_ : 0 ≤ l1) (l2 : ℝ),
        ((ρ * l1 + ε * l2 : ℝ) : EReal) + (((N : ℝ)⁻¹ : ℝ) : EReal) *
          ∑ i, max (⨆ y, ((ε⁻¹ * L y - (DX x0 (xh i) + DY y (yh i)) * l1 - l2 : ℝ) : EReal)) 0 := by sorry

end CondPortOT.SingDual
