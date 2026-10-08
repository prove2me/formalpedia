-- Prove2me | Theorems.Thm_ChinesePostman_Matching_parity_problem_eq_odd_node_matching
-- name    : ChinesePostman.Matching.parity_problem_eq_odd_node_matching
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:39:57.275125+00:00
-- url     : https://prove2.me/theorems/3fc6b5a4-61b8-4ed7-8b03-10f5928a358c
-- title:
--   §3, pp. 92–93 — parity optimum equals odd-node matching optimum
-- statement:
--   Let $G$ be a connected finite loopless multigraph with nonnegative edge lengths $c_e$. Write $T$ for its odd-degree nodes, $d(u,v)$ for attained shortest-path distances, $z(x)=\sum_ec_ex_e$ for the cost of a nonnegative integral parity solution, and $L(M)$ for the length of a 1-matching of $T$. There exists at least one 1-matching $M$ of $T$, and
--
--   $$
--   \forall M\;\exists x:\quad x_e\in\{0,1\},\quad z(x)\le L(M),
--   \qquad
--   \forall x\;\exists M:\quad L(M)\le z(x).
--   $$
--
--   Here the first quantifier ranges over 1-matchings and the second over parity solutions. Since 1-matchings of $T$ exist, the first clause also produces a parity solution, so both minima are attained and equal:
--
--   $$
--   \min\{z(x): x \text{ satisfies } (3.1)\text{–}(3.3)\}=\min\{L(M): M \text{ a 1-matching of } G_p\}.
--   $$
--
--   This is the reduction of the parity problem (3.1)–(3.4) to a minimum 1-matching on the complete graph $G_p$ of odd nodes with shortest-path lengths; together with §2 it reduces the Chinese postman problem to matching.
--
--
--
--   **Formalization Note** Distances require an attaining edge-simple path and a lower bound over every walk, so $d$ is never a junk infimum; connectivity makes this satisfiable. The odd-node set is computed from $G$, and a 1-matching of $G_p$ is a fixed-point-free involution $f$ of $T$ (identity off $T$) with $L(M)=\frac12\sum_{v\in T}d(v,f(v))$. The existence clause is not a hypothesis: it is a consequence (handshake lemma) stated so that the two minima are attained. The page derives the solution from an *optimum* matching; the first clause is stated for every matching, which the uncrossing step shows.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), pp. 92–93, §3, the 1-matching reduction, https://doi.org/10.1007/BF01580113

import Mathlib
import Definitions.Def_ChinesePostman_Matching_Setting

namespace ChinesePostman.Matching


/-- §3, pp. 92–93: parity solutions and perfect matchings of odd nodes
have the same attained minimum cost. -/
theorem parity_problem_eq_odd_node_matching
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (hG : Connected G) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e)
    (d : V → V → ℝ) (hd : ∀ i j, IsShortestPathLength G c i j (d i j)) :
    (∃ f : V → V, IsOddPerfectMatching G f) ∧
    (∀ f : V → V, IsOddPerfectMatching G f →
      ∃ x : E → ℕ, IsParitySolution G x ∧ (∀ e, x e ≤ 1) ∧
        cost c x ≤ matchingLength G d f) ∧
    (∀ x : E → ℕ, IsParitySolution G x →
      ∃ f : V → V, IsOddPerfectMatching G f ∧
        matchingLength G d f ≤ cost c x) := by sorry
end ChinesePostman.Matching
