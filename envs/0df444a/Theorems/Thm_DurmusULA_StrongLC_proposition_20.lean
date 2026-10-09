-- Prove2me | Theorems.Thm_DurmusULA_StrongLC_proposition_20
-- name    : DurmusULA.StrongLC.proposition_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:14.360983+00:00
-- url     : https://prove2.me/theorems/65de0731-1558-494c-be18-50c75ce423fb
-- title:
--   Proposition 20, p. 16 — V(x) = ‖x − x⋆‖² satisfies the drift (6) with λ = e^{−2m+γ̄L²}, c = 2(d + mM_s²)
-- statement:
--   Let $d\ge1$. Let $U$ satisfy **L1** (constant $L$) and **H3($M_s$)** (constants $m>0$, $M_s\ge0$), let $x^\star$ be a minimiser of $U$, and let $\bar\gamma\in(0,2mL^{-2})$. Put $V(x)=\|x-x^\star\|^2$,
--   $$\lambda=e^{-2m+\bar\gamma L^2},\qquad c=2(d+mM_s^2).$$
--   Then $\lambda<1$, $c>0$, and for every $\gamma\in(0,\bar\gamma]$ and $x\in\mathbb R^d$ the Euler kernel $R_\gamma(x,\cdot)=\mathcal N(x-\gamma\nabla U(x),2\gamma I_d)$ satisfies the Foster–Lyapunov drift condition (6):
--   $$R_\gamma V(x)=\int\|y-x^\star\|^2R_\gamma(x,dy)\le\lambda^\gamma V(x)+\gamma c .$$
--
--   Combined with Lemma 1 it controls the second moments of the ULA iterates uniformly in the number of steps.
--
--   **Formalization Note** The dimension is taken positive, as in the paper's Euclidean setting: at $d=0$ and $M_s=0$, the displayed $c$ is zero and cannot meet (6)'s $c>0$ requirement. The condition $\bar\gamma<2mL^{-2}$ is written $\bar\gamma L^2<2m$, which needs no division. (6) asks $\lambda\in[0,1)$; $\lambda>0$ is automatic. $R_\gamma V(x)$ is a lower Lebesgue integral. $x^\star$ is a bound variable with the hypothesis that it minimises $U$.
-- source:
--   Durmus and Moulines, Non-asymptotic convergence analysis for the Unadjusted Langevin Algorithm, arXiv:1507.05021v3, p. 16, Proposition 20; (6) p. 4; L1 p. 3; H3 p. 15

import Mathlib
import Definitions.Def_DurmusULA_StrongLC_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace

namespace DurmusULA.StrongLC

theorem proposition_20 (d : ℕ) (U : EthierKurtz.SDEState d → ℝ) (L m Ms γbar : ℝ)
    (xstar : EthierKurtz.SDEState d)
    (hd : 0 < d) (hL1 : L1 U L) (hH3 : H3 U m Ms) (hxstar : ∀ y, U xstar ≤ U y)
    (hγbar : 0 < γbar) (hγbarL : γbar * L ^ 2 < 2 * m) :
    Real.exp (-2 * m + γbar * L ^ 2) < 1 ∧ 0 < 2 * ((d : ℝ) + m * Ms ^ 2) ∧
    ∀ γ : ℝ, 0 < γ → γ ≤ γbar → ∀ x : EthierKurtz.SDEState d,
      ∫⁻ y, ENNReal.ofReal (‖y - xstar‖ ^ 2) ∂(eulerStep U γ x) ≤
        ENNReal.ofReal (Real.exp (-2 * m + γbar * L ^ 2) ^ γ * ‖x - xstar‖ ^ 2 +
          γ * (2 * ((d : ℝ) + m * Ms ^ 2))) := by sorry

end DurmusULA.StrongLC
