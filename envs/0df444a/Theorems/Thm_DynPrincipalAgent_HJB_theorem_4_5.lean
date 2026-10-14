-- Prove2me | Theorems.Thm_DynPrincipalAgent_HJB_theorem_4_5
-- name    : DynPrincipalAgent.HJB.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:35:13.533253+00:00
-- url     : https://prove2.me/theorems/6fc44676-2e5e-49aa-99e6-456062e50c57
-- title:
--   Theorem 4.5, p. 18 — u₁(θ; ·, ·) is the minimal continuous viscosity solution of (4.6) with boundary conditions (4.4)
-- statement:
--   Let Assumptions 2.2 and 3.1 hold and fix a type $\theta$. Let $u_1(\theta;t,x)$ be the principal's value when the current agent may quit once and every later hire is self-enforcing (3.9). Then:
--   1. for every $(t,x)\in D_\theta$ the set of values in (3.9) is nonempty and bounded above;
--   2. $u_1(\theta;\cdot,\cdot)$ is a continuous viscosity solution of
--   $$\mathcal L^\theta u(t,x)=0,\qquad(t,x)\in D_\theta,$$
--   and satisfies the boundary conditions (4.4): $u_1(\theta;t,\overline L^\theta_t)=-C_0(T-t)$, $u_1(\theta;T-,x)=0$ for $x\in(\underline L^\theta_T,0)$, and $u_1(\theta;t,\underline L^\theta_t+)\ge\overline u_0(t)$;
--   3. it is minimal: every continuous viscosity solution $u$ of (4.6) satisfying (4.4) has $u_1(\theta;t,x)\le u(t,x)$ on $D_\theta$.
--
--   This is the one-quitting case of the mission's main theorem.
--
--   **Formalization Note.** Viscosity solutions and the boundary conditions are those of the `Viscosity` and `SelfEnforcing` definition files. Item 1 is presupposed by the paper. No growth or boundedness condition is imposed on the competitors $u$, as in the paper.
-- source:
--   Zhang & Zhu, A Dynamic Principal Agent Problem with One-sided Commitment, arXiv:2208.06473v3, Theorem 4.5 and (4.4), p. 18

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_DynPrincipalAgent_HJB_Model
import Definitions.Def_DynPrincipalAgent_HJB_Viscosity
import Definitions.Def_DynPrincipalAgent_HJB_Controls
import Definitions.Def_DynPrincipalAgent_HJB_Quitting
import Definitions.Def_DynPrincipalAgent_HJB_SelfEnforcing

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open Peng1990.SMP

namespace DynPrincipalAgent.HJB

theorem theorem_4_5 {Θ : Type} [MeasurableSpace Θ] (M : Model Θ) (hM : M.Standing)
    {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) (θ : Θ) :
    (∀ p ∈ M.D θ, (M.valSetWith S (M.u0bar S) θ p.1.toNNReal p.2).Nonempty ∧
      BddAbove (M.valSetWith S (M.u0bar S) θ p.1.toNNReal p.2)) ∧
    M.IsContViscSol θ (M.u1 S θ) ∧
    M.BCwith θ (M.u0bar S) (M.u1 S θ) ∧
    (∀ u : ℝ → ℝ → ℝ, M.IsContViscSol θ u → M.BCwith θ (M.u0bar S) u →
      ∀ p ∈ M.D θ, M.u1 S θ p.1 p.2 ≤ u p.1 p.2) := by sorry

end DynPrincipalAgent.HJB
