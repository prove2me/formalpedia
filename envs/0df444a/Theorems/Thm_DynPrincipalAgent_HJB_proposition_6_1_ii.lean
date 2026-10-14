-- Prove2me | Theorems.Thm_DynPrincipalAgent_HJB_proposition_6_1_ii
-- name    : DynPrincipalAgent.HJB.proposition_6_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:37:42.522494+00:00
-- url     : https://prove2.me/theorems/34a1be46-1dd5-4bb5-9892-c817f141eccd
-- title:
--   Proposition 6.1 (ii), p. 31 — u_n converges to u_∞ uniformly, |u_n − u_∞| ≤ C/n
-- statement:
--   Let Assumptions 2.2 and 3.1 hold. There is a constant $C>0$ depending only on $T$, $C_0$, $\Lambda_0$, $\Lambda_1$ such that for every type $\theta$, every $(t,x)\in D_\theta$ and every $n\ge1$,
--   $$|u_n(\theta;t,x)-u_\infty(\theta;t,x)|\le\frac Cn.$$
--   Here $u_n$ is the principal's value when at most $n$ quittings are tolerated (5.1) and $u_\infty$ the value without restriction (6.1).
--
--   Uniform convergence transfers the dynamic programming principle and the regularity of $u_n$ to $u_\infty$.
--
--   **Formalization Note.** $C$ is chosen before the model, uniformly in $\theta$, $(t,x)$ and $n$.
-- source:
--   Zhang & Zhu, A Dynamic Principal Agent Problem with One-sided Commitment, arXiv:2208.06473v3, Proposition 6.1 (ii), (6.4), p. 31

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

theorem proposition_6_1_ii : ∀ (T : ℝ≥0) (C₀ Λ₀ Λ₁ : ℝ), ∃ C : ℝ, 0 < C ∧
    ∀ {Θ : Type} [MeasurableSpace Θ] (M : Model Θ),
      M.T = T → M.C₀ = C₀ → M.Λ₀ = Λ₀ → M.Λ₁ = Λ₁ → M.Standing →
    ∀ {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) (θ : Θ), ∀ p ∈ M.D θ,
      ∀ n : ℕ, 1 ≤ n → |M.uN S n θ p.1 p.2 - M.uInf S θ p.1 p.2| ≤ C / n := by sorry

end DynPrincipalAgent.HJB
