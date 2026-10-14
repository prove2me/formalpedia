-- Prove2me | Theorems.Thm_CondPortOT_NullFiber_proposition_4_3
-- name    : CondPortOT.NullFiber.proposition_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:35:11.106009+00:00
-- url     : https://prove2.me/theorems/531114ee-49cb-47ea-a8bf-cdc7cd7f3fb5
-- title:
--   Proposition 4.3 — for γ > 0 and ρ < ρ_max, the constraint ℚ(X ∈ 𝒩_γ(x₀)) > 0 can be replaced by ℚ(X ∈ 𝒩_γ(x₀)) ≥ ε̲ with an explicit LP value ε̲ > 0
-- statement:
--   Let $\mathcal X,\mathcal Y$ be Polish spaces, $(\hat x_i,\hat y_i)_{i\in[N]}$ samples with $N\ge1$, $x_0\in\mathcal X$, and $\gamma>0$. Assume Assumption 2.4 and the boundary regularity of $\mathcal N_\gamma(x_0)$, and let $0\le\rho<\rho_{\max}(x_0,\gamma)$. Define
--
--   $$\underline\varepsilon=\min\Big\{\frac1N\sum_{i\in\mathcal I_1}p_i:\ p\in[0,1]^N,\ \frac1N\sum_{i\in\mathcal I_1}d_i(1-p_i)\le\rho\Big\}.$$
--
--   Then the minimum is attained, $\underline\varepsilon>0$, and for every loss $\ell:\mathcal Y\to\mathbb R$
--
--   $$\sup_{\mathbb Q\in\mathbb B_\rho,\ \mathbb Q(X\in\mathcal N_\gamma(x_0))>0}\mathbb E_{\mathbb Q}\big[\ell(Y)\mid X\in\mathcal N_\gamma(x_0)\big]=\sup_{\mathbb Q\in\mathbb B_\rho,\ \mathbb Q(X\in\mathcal N_\gamma(x_0))\ge\underline\varepsilon}\mathbb E_{\mathbb Q}\big[\ell(Y)\mid X\in\mathcal N_\gamma(x_0)\big].$$
--
--   Since this holds for the loss $y\mapsto\ell(y,\alpha,\beta)$ of every portfolio decision $(\alpha,\beta)$, the distributionally robust conditional portfolio problem (12) with the degenerate constraint $\mathbb Q(X\in\mathcal N_\gamma(x_0))>0$ is equivalent to the problem with the explicit mass requirement $\underline\varepsilon$. This allows the duality theory for a positive mass requirement (Theorem 4.4) to be applied to (12) when $\rho<\rho_{\max}$.
--
--   **Formalization Note** "Equivalent" is formalized as equality of the inner suprema for every loss $\ell:\mathcal Y\to\mathbb R$, which implies equality of the min–max problems over any feasible set of $(\alpha,\beta)$. The page refers to model "(10)"; the problem meant is (12), the $\gamma>0$ problem, which is what the left side states. Values are in the extended reals, the expectation is $\int\ell^+-\int\ell^-$, and the mass $\mathbb Q(\cdot)$ is compared with $\underline\varepsilon$ through `ENNReal.ofReal`. The hypothesis $\rho\ge0$ is the paper's standing $\rho\in\mathbb R_+$; the boundary regularity (`BoundaryRegular`) is an addition, used by the proof's bound "$\mathbb E_{\pi_i}[\mathbb D_{\mathcal X}(X,\hat x_i)\mid X\notin\mathcal N_\gamma(x_0)]\,\pi_i(X\notin\mathcal N_\gamma(x_0))\ge d_i(1-\pi_i(X\in\mathcal N_\gamma(x_0)))$", which fails for a general continuous cost.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, p. 19, Proposition 4.3

import Mathlib
import Definitions.Def_CondPortOT_NullFiber_Setting

namespace CondPortOT.NullFiber

open MeasureTheory

theorem proposition_4_3 {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (γ : ℝ) (hγ : 0 < γ)
    (hA : Assumption24 DX DY x0 γ xh) (hH2 : CondPortOT.BigRadius.BoundaryRegular DX x0 γ xh)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ENNReal.ofReal ρ < CondPortOT.BigRadius.rhoMax DX DY xh yh x0 γ) :
    ∃ εl : ℝ, IsLeast (knapsackSet DX x0 γ xh ρ) εl ∧ 0 < εl ∧
      ∀ L : Y → ℝ,
        CondPortOT.SingUninf.worstCasePos DX DY xh yh x0 γ ρ L = CondPortOT.SingDual.worstCaseGe DX DY xh yh x0 γ ρ εl L := by sorry

end CondPortOT.NullFiber
