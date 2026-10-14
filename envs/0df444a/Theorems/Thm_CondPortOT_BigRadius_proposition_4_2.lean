-- Prove2me | Theorems.Thm_CondPortOT_BigRadius_proposition_4_2
-- name    : CondPortOT.BigRadius.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:44.68686+00:00
-- url     : https://prove2.me/theorems/1521ff01-273d-43b2-925d-9f61474592a1
-- title:
--   Proposition 4.2 — for γ > 0, ε = 0 and ρ > ρ_max(x₀, γ) the worst-case conditional expected loss equals sup_{y∈𝒴} ℓ(y)
-- statement:
--   Let $\mathcal X$ and $\mathcal Y$ be Polish spaces, $(\hat x_i,\hat y_i)_{i\in[N]}$ the data ($N\ge1$), $\hat{\mathbb P}$ its empirical distribution, and $\mathbb B_\rho$ the ball of radius $\rho$ around $\hat{\mathbb P}$ for the optimal transport cost with ground cost $\mathbb D_{\mathcal X}+\mathbb D_{\mathcal Y}$. Fix $x_0\in\mathcal X$ and a fiber radius $\gamma>0$, and let Assumption 2.4 hold. If
--   $$\rho>\rho_{\max}(x_0,\gamma)=\inf\big\{\mathbb W(\mathbb Q,\hat{\mathbb P}):\mathbb Q(X\in\mathcal N_\gamma(x_0))=0\big\},$$
--   then for every loss $\ell:\mathcal Y\to\mathbb R$
--   $$\sup_{\mathbb Q\in\mathbb B_\rho,\ \mathbb Q(X\in\mathcal N_\gamma(x_0))>0}\mathbb E_{\mathbb Q}\big[\ell(Y)\mid X\in\mathcal N_\gamma(x_0)\big]=\sup_{y\in\mathcal Y}\ell(y).$$
--
--   Once the budget suffices to move every sample out of the fiber, the robust conditional loss no longer depends on the data: it is the worst case over the whole return space. This is the negative result that motivates the strictly positive mass requirement of Proposition 4.3 and Theorem 4.4.
--
--   **Formalization Note** The loss $\ell(\cdot,\alpha,\beta)$ at a fixed portfolio $(\alpha,\beta)$ is an arbitrary function $L:\mathcal Y\to\mathbb R$; the theorem holds for every such $L$, hence for every feasible $(\alpha,\beta)$. Both sides are extended reals; the right side may be $+\infty$. The supremum ranges only over probability measures in the ball with strictly positive fiber mass ($\varepsilon=0$ with strict inequality, problem (12)). The hypothesis $\rho>\rho_{\max}$ is about $\rho_{\max}$ as defined, not its closed form (Proposition 4.1), and no boundary regularity beyond Assumption 2.4 is assumed.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, p. 19, Proposition 4.2 (proof pp. 46–47)

import Mathlib
import Definitions.Def_CondPortOT_BigRadius_Setting
open MeasureTheory RWPI.SqrtLasso ModelRiskOT.Duality

namespace CondPortOT.BigRadius

theorem proposition_4_2 {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (γ : ℝ) (hγ : 0 < γ) (hA : Assumption24 DX DY x0 γ xh)
    (ρ : ℝ) (hρ : rhoMax DX DY xh yh x0 γ < ENNReal.ofReal ρ) (L : Y → ℝ) :
    CondPortOT.SingUninf.worstCasePos DX DY xh yh x0 γ ρ L = ⨆ y, (L y : EReal) := by sorry

end CondPortOT.BigRadius
