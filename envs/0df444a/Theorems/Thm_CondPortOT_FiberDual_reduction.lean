-- Prove2me | Theorems.Thm_CondPortOT_FiberDual_reduction
-- name    : CondPortOT.FiberDual.reduction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:35:09.735049+00:00
-- url     : https://prove2.me/theorems/ff855c2e-a257-40ea-93f9-bd6c3659f728
-- title:
--   Proof of Theorem 4.4, pp. 48–49 — the worst case reduces to a program over pᵢ ∈ [0, 1] and μ₀ⁱ ∈ ℳ(𝒴)
-- statement:
--   Assume the hypotheses of Theorem 4.4: $\gamma>0$, $\varepsilon>0$, $\rho>\rho_{\min}(x_0,\gamma,\varepsilon)$, Assumption 2.4, the boundary-regularity predicate, and a measurable loss $\ell:\mathcal Y\to\mathbb R$. Let $d_i$ be the boundary distances (14) and $\mathcal I_1,\mathcal I_2$ the index sets (13). Then
--   $$\sup_{\substack{\mathbb Q\in\mathbb B_\rho\\ \mathbb Q(X\in\mathcal N_\gamma(x_0))\ge\varepsilon}}\mathbb E_{\mathbb Q}[\ell(Y)\mid X\in\mathcal N_\gamma(x_0)]=\sup\ \frac{\sum_{i\in[N]}p_i\,\mathbb E_{\mu_0^i}[\ell(Y)]}{\sum_{i\in[N]}p_i},$$
--   where the supremum on the right is over $p\in[0,1]^N$ and probability measures $\mu_0^1,\dots,\mu_0^N$ on $\mathcal Y$ subject to
--   $$\sum_{i\in\mathcal I_1}\Big(p_i\,\mathbb E_{\mu_0^i}[\mathbb D_{\mathcal Y}(Y,\hat y_i)]+(1-p_i)d_i\Big)+\sum_{i\in\mathcal I_2}\Big(p_i\,\mathbb E_{\mu_0^i}[\mathbb D_{\mathcal Y}(Y,\hat y_i)]+p_id_i\Big)\le N\rho,\qquad\sum_{i\in[N]}p_i\ge N\varepsilon.$$
--
--   Here $p_i$ is the share of sample $i$ that ends up in the fiber and $\mu_0^i$ the law of $Y$ for that share: samples in the fiber leave it at cost $d_i$, samples outside enter it at cost $d_i$. This turns the supremum over measures on $\mathcal X\times\mathcal Y$ into one over finitely many weights and measures on $\mathcal Y$.
--
--   **Formalization Note.** The cost constraint is written in $[0,\infty]$ (each term through `ENNReal.ofReal`, expectations of the cost as lower integrals). The objective is computed in the extended reals with the expectations $\int\ell^+-\int\ell^-$; since $\sum_ip_i\ge N\varepsilon>0$, the division is never by zero. The paper writes "for any $i\in\mathcal I$" and "$\sum_{i\in\mathcal I}p_i\ge N\varepsilon$"; $\mathcal I=[N]$ is meant and used.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, pp. 48–49, proof of Theorem 4.4, display (25) and the display that follows it

import Mathlib
import Definitions.Def_CondPortOT_FiberDual_Setting
open MeasureTheory RWPI.SqrtLasso ModelRiskOT.Duality

namespace CondPortOT.FiberDual

theorem reduction {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (γ : ℝ) (hγ : 0 < γ) (hA : CondPortOT.BigRadius.Assumption24 DX DY x0 γ xh)
    (hH2 : CondPortOT.BigRadius.BoundaryRegular DX x0 γ xh)
    (ε : ℝ) (hε : 0 < ε) (ρ : ℝ) (hρ : CondPortOT.SingDual.rhoMin DX DY xh yh x0 γ ε < ENNReal.ofReal ρ)
    (L : Y → ℝ) (hL : Measurable L) :
    CondPortOT.SingDual.worstCaseGe DX DY xh yh x0 γ ρ ε L =
      ⨆ (p : Fin N → ℝ) (μ : Fin N → Measure Y)
        (_ : (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i, IsProbabilityMeasure (μ i)) ∧
          (∑ i ∈ CondPortOT.BigRadius.I1 DX x0 γ xh,
              (ENNReal.ofReal (p i) * ∫⁻ y, ENNReal.ofReal (DY y (yh i)) ∂(μ i) +
                ENNReal.ofReal ((1 - p i) * CondPortOT.BigRadius.bdDist DX x0 γ xh i)) +
            ∑ i ∈ (CondPortOT.BigRadius.I1 DX x0 γ xh)ᶜ,
              (ENNReal.ofReal (p i) * ∫⁻ y, ENNReal.ofReal (DY y (yh i)) ∂(μ i) +
                ENNReal.ofReal (p i * CondPortOT.BigRadius.bdDist DX x0 γ xh i))
            ≤ ENNReal.ofReal (N * ρ)) ∧
          (N : ℝ) * ε ≤ ∑ i, p i),
        (((∑ i, p i)⁻¹ : ℝ) : EReal) *
          ∑ i, ((p i : ℝ) : EReal) * extIntegral (μ i) (fun y => (L y : EReal)) := by sorry

end CondPortOT.FiberDual
