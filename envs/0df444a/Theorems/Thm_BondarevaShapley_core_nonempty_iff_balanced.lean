-- Prove2me | Theorems.Thm_BondarevaShapley_core_nonempty_iff_balanced
-- name    : BondarevaShapley.core_nonempty_iff_balanced
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-05T01:36:41.292765+00:00
-- url     : https://prove2.me/theorems/bbf8a5ff-900f-4143-963e-0d96c27af4c0
-- title:
--   Bondareva–Shapley theorem: the core of a TU game is nonempty iff the game is balanced
-- statement:
--   This is the Bondareva–Shapley theorem: the exact criterion for a cooperative game with transferable utility to have a nonempty core.
--
--   Let $N$ be a finite nonempty set of players. A *game* (with transferable utility) on $N$ is a function $v : 2^N \to \mathbb{R}$ assigning a worth $v(S)$ to every coalition $S \subseteq N$, with $v(\emptyset) = 0$. For a payoff vector $x \in \mathbb{R}^N$ and a coalition $S$ write $x(S) = \sum_{i \in S} x_i$. The *core* of $(N, v)$ is
--   $$
--   C(N, v) = \{\, x \in \mathbb{R}^N : x(N) = v(N) \text{ and } x(S) \ge v(S) \text{ for all } S \subseteq N \,\}.
--   $$
--
--   A collection $\mathcal{B}$ of nonempty subsets of $N$ is *balanced* if there are positive numbers $\delta_S > 0$, $S \in \mathcal{B}$ (a system of *balancing weights*), such that
--   $$
--   \sum_{S \in \mathcal{B},\; S \ni i} \delta_S = 1 \qquad \text{for every player } i \in N,
--   $$
--   that is, $\sum_{S \in \mathcal{B}} \delta_S \chi_S = \chi_N$, where $\chi_S$ is the indicator vector of $S$. The game $(N, v)$ is *balanced* if for every balanced collection $\mathcal{B}$ with every system of balancing weights $(\delta_S)_{S \in \mathcal{B}}$,
--   $$
--   \sum_{S \in \mathcal{B}} \delta_S \, v(S) \le v(N).
--   $$
--
--   **Theorem (Bondareva 1963, Shapley 1967).** The core of $(N, v)$ is nonempty if and only if $(N, v)$ is balanced:
--   $$
--   C(N, v) \neq \emptyset \iff (N, v) \text{ is balanced}.
--   $$
--
--   The theorem characterizes, by finitely many linear inequalities on $v$, exactly when the coalition constraints $x(S) \ge v(S)$ can be met by an efficient allocation of $v(N)$. It is the standard tool for proving that the cores of market games, linear production games, flow games and assignment games are nonempty, and it complements the results on cores of convex games.
--
--   **Formalization Note** Players form a finite nonempty type `N`, coalitions are `Finset N`, and the game is a function `v : Finset N → ℝ` with the hypothesis `v ∅ = 0`. A balanced collection is a finite set `B` of coalitions with `∅ ∉ B`, together with weights `δ : Finset N → ℝ` that are positive on `B` (values of `δ` off `B` are irrelevant) and satisfy $\sum_{S \in B,\ i \in S} \delta_S = 1$ for every player $i$. The core is written out inline as the existence of $x : N \to \mathbb{R}$ with $\sum_i x_i = v(N)$ and $v(S) \le x(S)$ for every coalition $S$.
-- source:
--   B. Peleg and P. Sudhölter, Introduction to the Theory of Cooperative Games, 2nd ed., Theory and Decision Library C 34, Springer, 2007, Chapter 3 (The Core), Section 3.1 (The Bondareva–Shapley Theorem): definition of balanced collections and balanced games, and Theorem 3.1.4. Original results: O. N. Bondareva, Some applications of linear programming methods to the theory of cooperative games, Problemy Kibernetiki 10 (1963) 119–139; L. S. Shapley, On balanced sets and cores, Naval Research Logistics Quarterly 14 (1967) 453–460.

import Mathlib

namespace BondarevaShapley

/-- Bondareva–Shapley theorem (Peleg–Sudhölter, Theorem 3.1.4): a TU game `(N, v)` with
`v ∅ = 0` has a nonempty core iff it is balanced, i.e. for every balanced collection `B`
of nonempty coalitions with (positive) balancing weights `δ`, `∑_{S ∈ B} δ_S v(S) ≤ v(N)`. -/
theorem core_nonempty_iff_balanced {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]
    (v : Finset N → ℝ) (hv : v ∅ = 0) :
    (∃ x : N → ℝ, ∑ i, x i = v Finset.univ ∧ ∀ S : Finset N, v S ≤ ∑ i ∈ S, x i) ↔
      ∀ (B : Finset (Finset N)) (δ : Finset N → ℝ),
        ∅ ∉ B → (∀ S ∈ B, 0 < δ S) →
        (∀ i : N, ∑ S ∈ B.filter (fun S => i ∈ S), δ S = 1) →
        ∑ S ∈ B, δ S * v S ≤ v Finset.univ := by sorry

end BondarevaShapley
