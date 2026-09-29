-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_discounted_bellman_solution
-- name    : BanditAlgorithm.mdp_discounted_bellman_solution
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T15:09:47.005017+00:00
-- url     : https://prove2.me/theorems/8fb4db1d-cd73-4e90-b6e6-55f42d163e1d
-- title:
--   Existence of a discounted Bellman solution for a finite MDP
-- statement:
--   Let $M$ be a finite MDP with $S \ge 1$ states, $A \ge 1$ actions, transition rows $P_a(s,\cdot)$ and rewards $r_a(s) \in [0,1]$, and let $\gamma \in [0,1)$ be a discount factor. Then there are a value function $V : \mathcal{S} \to \mathbb{R}$ with $V(s) \in [0, (1-\gamma)^{-1}]$ and a map $f : \mathcal{S} \to \mathcal{A}$ such that
--
--   $$r_a(s) + \gamma \langle P_a(s), V\rangle \;\le\; V(s) \quad \text{for every } a, \qquad V(s) \;=\; r_{f(s)}(s) + \gamma \langle P_{f(s)}(s), V\rangle .$$
--
--   Equivalently $V(s) = \max_a \big(r_a(s) + \gamma \langle P_a(s), V\rangle\big)$ for every state $s$, and $f$ is a greedy — hence optimal — deterministic memoryless policy for the $\gamma$-discounted criterion. The conclusion is stated as the conjunction of the inequality and the attaining action rather than through a maximum, so that it can be used without carrying a nonemptiness proof for the action set.
--
--   The proof is the Banach fixed point theorem. The discounted Bellman optimality operator
--
--   $$(T v)(s) \;=\; \max_a \big( r_a(s) + \gamma \langle P_a(s), v \rangle \big)$$
--
--   is a $\gamma$-contraction of $\mathbb{R}^{\mathcal S}$ in the supremum norm: for each fixed action the map $v \mapsto \gamma \langle P_a(s), v\rangle$ moves by at most $\gamma \|u - v\|_\infty$ because $P_a(s)$ is a probability vector, and a maximum over a finite set of uniformly close functions is uniformly close. The space $\mathbb{R}^{\mathcal S}$ is complete, so $T$ has a fixed point $V$; the inequality is the definition of the maximum and the equality is its attainment. The bounds come from evaluating the fixed point equation at a maximising and at a minimising state: $\max_s V(s) \le 1 + \gamma \max_s V(s)$ gives $\max_s V \le (1-\gamma)^{-1}$, and $\min_s V(s) \ge \gamma \min_s V(s)$ gives $\min_s V \ge 0$.
--
--   This is the computational core of value iteration, and the starting point of the vanishing-discount proof of the average-reward optimality equation (Theorem 38.2 of Lattimore and Szepesvári, whose proof is left to their Exercise 38.10): the rescaled pairs $\big((1-\gamma)\max_s V_\gamma(s),\, V_\gamma\big)$ solve the average-reward Bellman inequality, and a limit along $\gamma \uparrow 1$ solves the optimality equation.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Section 38.2 (the discounted value function underlying Theorem 38.2 and Exercise 38.10); Puterman, Markov Decision Processes (Wiley 1994), Chapter 6 (discounted MDPs, the Bellman operator as a contraction).

import Definitions.Def_FiniteMDPLearning
import Mathlib.Topology.MetricSpace.Contracting

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.mdp_discounted_bellman_solution {S A : ℕ} (hS : 0 < S) (hA : 0 < A)
    (M : FiniteMDP S A) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∃ (V : Fin S → ℝ) (f : Fin S → Fin A),
      (∀ s, V s ∈ Set.Icc (0 : ℝ) (1 / (1 - γ))) ∧
      (∀ s a, M.r s a + γ * ∑ s', (M.P s a s' : ℝ) * V s' ≤ V s) ∧
      (∀ s, V s = M.r s (f s) + γ * ∑ s', (M.P s (f s) s' : ℝ) * V s') := by
  sorry
