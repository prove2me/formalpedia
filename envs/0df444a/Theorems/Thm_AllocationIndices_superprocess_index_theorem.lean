-- Prove2me | Theorems.Thm_AllocationIndices_superprocess_index_theorem
-- name    : AllocationIndices.superprocess_index_theorem
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T02:50:34.473426+00:00
-- url     : https://prove2.me/theorems/b7d734d1-87ab-467d-988b-1948329ad570
-- title:
--   Theorem 4.3: under Condition D, the index policy that continues a superprocess of maximal ν(S_i, x_i) with its Condition-D control is optimal for a SFAS
-- statement:
--   **Theorem 4.3 (Index theorem for a SFAS).** A policy for a simple family of alternative superprocesses comprised of $S_1, \dots, S_n$, which all satisfy Condition D, is optimal if it is an index policy with respect to $\nu(S_1, \cdot, \cdot), \dots, \nu(S_n, \cdot, \cdot)$.
--
--   Formally, in discrete time: $D$ a decision process on a countable state space $S$ with finite control type $U$ and bounded rewards, $a \in (0,1)$, and $g$ a Condition-D control for $D$ ($g$ feasible, and whenever it is optimal to select $S$ in state $x$ in $\{S, \Lambda(\lambda)\}$ it is optimal to apply $g(x)$; the $n$ superprocesses of the family are copies of $D$, a family of distinct superprocesses being the disjoint-union case). If a policy $\pi$ for the family of $n$ superprocesses at every decision time almost surely continues a superprocess $i$ of maximal index $\nu(D, x_i) = \max_{u \in \Gamma(x_i)} \nu(D, x_i, u)$ and applies the control $g(x_i)$, then $\pi$ is optimal: it is feasible and its payoff equals the supremum of the payoffs of all feasible policies from every initial state-vector. Since $\nu(D, x, g(x)) = \nu(D, x)$ (Note 4.2 at $\lambda = \nu(D, x)$), $\pi$ is an index policy with respect to $\nu(D, \cdot, \cdot)$.
--
--   **Why the control is pinned to $g$.** The book's proof runs the index policy with the controls $g_i(x_i)$ of Condition D. An index policy that breaks a tie among controls differently need not be optimal. Take $n = 1$, $a = 1/2$ and a state $x$ with two controls: $u$ pays $1$ and leads to a state paying $1$ forever, and $u'$ pays $1$ and leads to a state paying $0$ forever. Both have index $1$, Condition D holds with $g(x) = u$, and the index policy that applies $u'$ earns $1$ against $2$.
--
--   With singleton control sets this is Theorem 2.1 (the proved platform theorem). The book's proof reduces the semi-Markov case to stochastic discounting and runs a prevailing-stake argument; here the family is Markov with unit decision intervals.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §4.3 pp. 83-85, Theorem 4.3 (index theorem for a SFAS, Whittle 1980) with its proof; the control applied is the Condition-D control g, as in the proof, since an index policy breaking ties among controls otherwise need not be optimal

import Definitions.Def_AllocationIndices_Superprocess

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

theorem superprocess_index_theorem {S U : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] [MeasurableSpace U] [Fintype U] [Nonempty U]
    [MeasurableSingletonClass U] (D : DecisionProcess S U) (hD : D.BoundedRewards)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {g : S → U} (hg : IsConditionDControl D a g)
    {n : ℕ} {π : SFASPolicy n S U} (hπ : IsSuperIndexPolicy D a g π) :
    IsOptimalSFASPolicy D a π := by sorry

end AllocationIndices
