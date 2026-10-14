-- Prove2me | Theorems.Thm_DynPrincipalAgent_HJB_proposition_6_2
-- name    : DynPrincipalAgent.HJB.proposition_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:33:21.704186+00:00
-- url     : https://prove2.me/theorems/50fb5621-d372-4494-9d75-417f2b056964
-- title:
--   Proposition 6.2, p. 31 — u_∞ is decreasing in x and uniformly continuous, ū_∞ is bounded and continuous, and (6.6) holds
-- statement:
--   Let Assumptions 2.2 and 3.1 hold. Then:
--   1. $u_\infty(\theta;t,\cdot)$ is nonincreasing on $(\underline L^\theta_t,\overline L^\theta_t]$ for $t\in[0,T)$; in particular $V^P_\infty(\theta;t)=u_\infty(\theta;t,R^\theta_t)$, and thus $\overline u_\infty(t)=V^P_\infty(t)-c^P_t$;
--   2. $u_\infty$ is uniformly continuous in $D_\theta$, uniformly in $\theta$: for every $\varepsilon>0$ there is $\delta>0$ such that $|u_\infty(\theta;t_1,x_1)-u_\infty(\theta;t_2,x_2)|<\varepsilon$ whenever $\theta\in\Theta$, $(t_i,x_i)\in D_\theta$, $|t_1-t_2|<\delta$ and $|x_1-x_2|<\delta$;
--   3. for every $t\in[0,T]$ the family $\{u_\infty(\theta;t,R^\theta_t)\}_\theta$ is bounded above, and $\overline u_\infty$ is bounded and uniformly continuous on $[0,T]$ with $\overline u_\infty(T)=-c^P_T$;
--   4. $u_\infty$ satisfies the boundary conditions
--   $$u_\infty(\theta;t,\overline L^\theta_t)=-C_0(T-t),\qquad u_\infty(\theta;T-,x)=0\ \ (x\in(\underline L^\theta_T,0)),\qquad u_\infty(\theta;t,\underline L^\theta_t+)\ge\overline u_\infty(t).\qquad(6.6)$$
--
--   **Formalization Note.** "Decreasing" is the paper's word for nonincreasing. The bounded-above clause in 3 makes the supremum over types in (6.5) a genuine one. The boundary conditions are those of the `Viscosity` definition file, with $\overline u_\infty$ built from $u_\infty$ itself.
-- source:
--   Zhang & Zhu, A Dynamic Principal Agent Problem with One-sided Commitment, arXiv:2208.06473v3, Proposition 6.2 and (6.6), p. 31

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_DynPrincipalAgent_HJB_Model
import Definitions.Def_DynPrincipalAgent_HJB_Viscosity
import Definitions.Def_DynPrincipalAgent_HJB_Controls
import Definitions.Def_DynPrincipalAgent_HJB_Quitting

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open Peng1990.SMP

namespace DynPrincipalAgent.HJB

theorem proposition_6_2 {Θ : Type} [MeasurableSpace Θ] (M : Model Θ) (hM : M.Standing)
    {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) :
    -- (i)
    (∀ θ : Θ, ∀ t : ℝ, 0 ≤ t → t < (M.T : ℝ) →
      AntitoneOn (M.uInf S θ t) (Ioc (M.Lund θ t) (M.Lbar θ t)) ∧
      M.VInf S θ t = M.uInf S θ t (M.R θ t)) ∧
    (∀ t : ℝ, 0 ≤ t → t < (M.T : ℝ) → M.uInfBar S t = M.VInfAll S t - M.cP t) ∧
    -- (ii)
    (∀ ε > 0, ∃ δ > 0, ∀ θ : Θ, ∀ p ∈ M.D θ, ∀ q ∈ M.D θ,
      |p.1 - q.1| < δ → |p.2 - q.2| < δ → |M.uInf S θ p.1 p.2 - M.uInf S θ q.1 q.2| < ε) ∧
    -- (iii)
    (∀ t ∈ Icc (0 : ℝ) M.T, BddAbove (Set.range fun θ : Θ => M.uInf S θ t (M.R θ t))) ∧
    (∃ K : ℝ, ∀ t ∈ Icc (0 : ℝ) M.T, |M.uInfBar S t| ≤ K) ∧
    UniformContinuousOn (M.uInfBar S) (Icc (0 : ℝ) M.T) ∧
    M.uInfBar S M.T = -M.cP M.T ∧
    -- (iv)
    M.BC6_6 (M.uInf S) := by sorry

end DynPrincipalAgent.HJB
