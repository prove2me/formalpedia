-- Prove2me | Theorems.Thm_AllocationIndices_conditionD_optimal_control_iff
-- name    : AllocationIndices.conditionD_optimal_control_iff
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T02:48:19.015637+00:00
-- url     : https://prove2.me/theorems/a27f9858-45d6-4d22-810f-aa93cea4a8a6
-- title:
--   Note 4.2 (corrected): under Condition D, S is selected in {S, Λ(λ)} iff ν(S, x) ≥ λ, and at λ = ν(S, x) a control u is optimal iff ν(S, x, u) = ν(S, x)
-- statement:
--   **Note 4.2.** If a superprocess $S$ satisfies Condition D, a control $u \in \Gamma(x)$ is optimal for $\{S, \Lambda\}$ if and only if $\nu(S, x, u) = \nu(S, x) \ge \lambda$. This follows by supposing that $\Lambda$ in the statement of Condition D has the parameter $\nu(S, x)$.
--
--   **Stated here, corrected.** For a decision process on a countable state space with bounded rewards, $a \in (0,1)$, satisfying Condition D, and every state $x$:
--   1. for every $\lambda$, it is optimal to select $S$ in state $x$ in the SFAS $\{S, \Lambda(\lambda)\}$ (some optimal policy continues $S$ at time $0$ from $(x, \Lambda)$) if and only if $\lambda \le \nu(S, x) = \max_{v \in \Gamma(x)} \nu(S, x, v)$;
--   2. for $\lambda = \nu(S, x)$, the parameter the note's own justification uses, a control $u \in \Gamma(x)$ is optimal to apply (some optimal policy continues $S$ with $u$ at time $0$ from $(x, \Lambda)$) if and only if $\nu(S, x, u) = \nu(S, x)$.
--
--   **Why not every $\lambda$.** The printed equivalence fails for $\lambda < \nu(S, x)$, in both directions. Take $a = 1/2$ and a state $x$ with two controls. $u$ pays $1$ and leads to a state paying $1$ forever. $u'$ pays $1$ and leads to a state paying $0$ forever. Both have index $1 = \nu(S, x)$, and Condition D holds with $g(x) = u$. At $\lambda = 1/2$, applying $u'$ earns $1 + 1/2 = 3/2$ against $2$, so $u'$ is not optimal, although $\nu(S, x, u') = \nu(S, x) \ge \lambda$. Conversely, let $u$ pay $1$ and then $0$ forever and $u'$ pay $0.9$ and then $0.1$ forever. Then $\nu(S, x) = 1 > \nu(S, x, u') = 0.9$, Condition D holds with $g(x) = u$, and at $\lambda = 0$ both controls earn $1$, so $u'$ is optimal. At $\lambda = \nu(S, x)$ the note is right: selecting $S$ is exactly as good as retiring, and a control is optimal exactly when some stationary policy starting with it has index $\nu(S, x)$ (the constrained stopping problem has an optimal stationary policy, so the supremum in (4.1) is attained where it matters).
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §4.2 p. 83, Note 4.2; stated at the parameter λ = ν(S, x) the note itself uses, since the printed claim fails for λ < ν(S, x)

import Definitions.Def_AllocationIndices_Superprocess

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

theorem conditionD_optimal_control_iff {S U : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] [MeasurableSpace U] [Fintype U] [Nonempty U]
    [MeasurableSingletonClass U] (D : DecisionProcess S U) (hD : D.BoundedRewards)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hcond : ConditionD D a) (x : S) :
    (∀ lam : ℝ, OptimalToSelect D a lam x ↔ lam ≤ superIndexMax D a x) ∧
    (∀ u ∈ D.avail x, OptimalToApply D a (superIndexMax D a x) x u ↔
      superIndex D a x u = superIndexMax D a x) := by sorry

end AllocationIndices
