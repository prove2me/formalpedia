-- Prove2me | Theorems.Thm_CondPortOT_NullFiber_inf_mass_eq
-- name    : CondPortOT.NullFiber.inf_mass_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:35:21.355268+00:00
-- url     : https://prove2.me/theorems/90dd774d-77d7-48b7-b058-35171bd5e1d7
-- title:
--   Proof of Proposition 4.3, pp. 47–48 — for ρ > 0 the minimal fiber mass equals the LP value min{N⁻¹Σ_{ℐ₁} pᵢ : N⁻¹Σ_{ℐ₁} dᵢ(1 − pᵢ) ≤ ρ}
-- statement:
--   Let $\gamma>0$, let Assumption 2.4 and the boundary regularity hold, and let $\rho>0$. Then the linear program
--
--   $$\underline\varepsilon=\min\Big\{\frac1N\sum_{i\in\mathcal I_1}p_i:\ p\in[0,1]^N,\ \frac1N\sum_{i\in\mathcal I_1}d_i(1-p_i)\le\rho\Big\}$$
--
--   attains its minimum, and this minimum is the smallest fiber mass over the ambiguity set:
--
--   $$\inf_{\mathbb Q\in\mathbb B_\rho}\mathbb Q\big(X\in\mathcal N_\gamma(x_0)\big)=\underline\varepsilon.$$
--
--   Here $p_i$ is the fraction of the $i$-th sample left inside the fiber and $d_i(1-p_i)$ is the cost of pushing the rest just outside; samples of $\mathcal I_2$ lie outside the fiber and stay there at no cost. This identifies the explicit lower bound $\underline\varepsilon$ of Proposition 4.3, a fractional knapsack problem.
--
--   **Formalization Note** The hypothesis is $\rho>0$, whereas the proof on the page claims the identity for every $\rho<\rho_{\max}(x_0,\gamma)$, including $\rho=0$. At $\rho=0$ the identity can fail: with $\mathcal X=\mathbb R$, $\mathbb D_{\mathcal X}(x,x')=|x-x'|$, $x_0=0$, $\gamma=1$, $\hat x_1=1$ (on the boundary, $d_1=0$) and $\hat x_2=0$ ($d_2=1$), the ball $\mathbb B_0=\{\widehat{\mathbb P}\}$ gives fiber mass $1$, while the LP value is $1/2$. No upper bound on $\rho$ is needed. The minimum is stated as attained (`IsLeast`), as "min" says; the infimum over $\mathbb B_\rho$ is in $[0,\infty]$ and is compared through `ENNReal.ofReal`.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, pp. 47–48, proof of Proposition 4.3 ("Next, we turn to how to evaluate ε̲ …")

import Mathlib
import Definitions.Def_CondPortOT_NullFiber_Setting

namespace CondPortOT.NullFiber

open MeasureTheory

theorem inf_mass_eq {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (γ : ℝ) (hγ : 0 < γ)
    (hA : Assumption24 DX DY x0 γ xh) (hH2 : CondPortOT.BigRadius.BoundaryRegular DX x0 γ xh)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ εl : ℝ, IsLeast (knapsackSet DX x0 γ xh ρ) εl ∧
      (⨅ (Q : Measure (X × Y)) (_ : CondPortOT.SingUninf.InBall DX DY xh yh ρ Q), Q (CondPortOT.SingUninf.fiber DX x0 γ)) =
        ENNReal.ofReal εl := by sorry

end CondPortOT.NullFiber
