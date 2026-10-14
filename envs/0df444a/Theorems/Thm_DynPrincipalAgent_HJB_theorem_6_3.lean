-- Prove2me | Theorems.Thm_DynPrincipalAgent_HJB_theorem_6_3
-- name    : DynPrincipalAgent.HJB.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:33:28.549273+00:00
-- url     : https://prove2.me/theorems/a7013829-a357-43d4-b22c-28884bb220e8
-- title:
--   Theorem 6.3, p. 31 — the principal's value function u_∞ is the minimal continuous viscosity solution of the HJB system (4.6) with boundary conditions (6.6)
-- statement:
--   Let Assumptions 2.2 and 3.1 hold. A principal hires agents of types $\theta\in\Theta$; each agent may quit when his continuation utility reaches the lower barrier $\underline L^\theta$, and the principal then pays $c^P$ and hires a new agent. Let $u_\infty(\theta;t,x)$ be the principal's value (6.1) when she hires an agent of type $\theta$ at time $t$ with continuation utility $x$. Then:
--   1. for every $\theta$ and $(t,x)\in D_\theta$ the set of values in (6.1) is nonempty and bounded above, so $u_\infty$ is a real-valued function;
--   2. for every $\theta$, $u_\infty(\theta;\cdot,\cdot)$ is a continuous viscosity solution of the HJB equation
--   $$\partial_tu+\sup_{\eta\le C_0,\ z\in\mathbb R}\Big[\tfrac12|z|^2\partial_{xx}u-\big[f(\theta;t,\eta)+\tilde H(\theta;t,z)\big]\partial_xu+I^h(\theta;t,z)-\eta\Big]=0\quad\text{on }D_\theta;$$
--   3. the family $\{u_\infty(\theta;\cdot,\cdot)\}_\theta$ satisfies the boundary conditions (6.6);
--   4. it is minimal: if $\{u(\theta;\cdot,\cdot)\}_{\theta\in\Theta}$ is any family of continuous viscosity solutions of these equations satisfying (6.6), with the boundary function at the lower barrier $\overline u(t)=\sup_\theta u(\theta;t,R^\theta_t)-c^P_t$ built from $u$ itself, then $u_\infty(\theta;t,x)\le u(\theta;t,x)$ for every $\theta$ and $(t,x)\in D_\theta$.
--
--   Because the boundary condition at the lower barrier involves the whole family, the equations for different types are coupled: the characterisation is for an infinite system of HJB equations.
--
--   **Formalization Note.** Item 1 is presupposed by the paper and makes the real supremum genuine. Viscosity solutions are tested on the interior $O_\theta$ with $C^2$ test functions, continuity is on $D_\theta$, and (6.6) is read with a real right limit at $\underline L^\theta_t$ compared against every $u(\theta';t,R^{\theta'}_t)-c^P_t$ (see the `Viscosity` definition file). No boundedness or growth condition is imposed on competitors, as in the paper.
-- source:
--   Zhang & Zhu, A Dynamic Principal Agent Problem with One-sided Commitment, arXiv:2208.06473v3, Theorem 6.3, p. 31

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

theorem theorem_6_3 {Θ : Type} [MeasurableSpace Θ] (M : Model Θ) (hM : M.Standing)
    {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) :
    (∀ θ : Θ, ∀ p ∈ M.D θ,
      (M.valSetInf S θ p.1.toNNReal p.2).Nonempty ∧ BddAbove (M.valSetInf S θ p.1.toNNReal p.2)) ∧
    (∀ θ : Θ, M.IsContViscSol θ (M.uInf S θ)) ∧
    M.BC6_6 (M.uInf S) ∧
    (∀ u : Θ → ℝ → ℝ → ℝ, (∀ θ : Θ, M.IsContViscSol θ (u θ)) → M.BC6_6 u →
      ∀ θ : Θ, ∀ p ∈ M.D θ, M.uInf S θ p.1 p.2 ≤ u θ p.1 p.2) := by sorry

end DynPrincipalAgent.HJB
