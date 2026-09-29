-- Prove2me | Theorems.Thm_AssignmentGame_CoreLP_primal_max_eq_worth
-- name    : AssignmentGame.CoreLP.primal_max_eq_worth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:14:08.829946+00:00
-- url     : https://prove2.me/theorems/22b9aefd-0cf9-4240-b468-1e6636026e88
-- title:
--   Sec. 3.1 (quoting Dantzig) — the assignment LP attains its maximum at a 0/1 point, and $z_{\max} = v(M \cup N)$
-- statement:
--   Let $M$ and $N$ be finite sets and $a = (a_{ij})$ a matrix with $a_{ij} \ge 0$. Consider the linear program (3.1)–(3.2): maximise
--   $$z = \sum_{i \in M}\sum_{j \in N} a_{ij} x_{ij}$$
--   over $x_{ij} \ge 0$ with $\sum_{i \in M} x_{ij} \le 1$ for each $j \in N$ and $\sum_{j \in N} x_{ij} \le 1$ for each $i \in M$. Then
--
--   1. every feasible $x$ has $z(x) \le v(M \cup N)$, the worth (2.6) of the all-player coalition; and
--   2. some feasible $x$ with every $x_{ij} \in \{0, 1\}$ attains $z(x) = v(M \cup N)$.
--
--   Together: the maximum $z_{\max}$ of the LP exists, is attained at a $0/1$ point, and equals $v(M \cup N)$. The paper quotes the integrality statement from Dantzig (p. 318); this is its specialisation to the rectangular assignment polytope with inequality constraints.
-- source:
--   Shapley and Shubik, The Assignment Game I: The Core, Int. J. Game Theory 1 (1971), p. 117, Sec. 3.1, Eqs. (3.1)-(3.2) and z_max = v(M ∪ N) (quoting Dantzig, Linear Programming and Extensions, p. 318)

import Mathlib
import Definitions.Def_AssignmentGame_CoreLP_Game

open Finset

namespace AssignmentGame.CoreLP

theorem primal_max_eq_worth {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    (∀ x : M → N → ℝ, PrimalFeasible x → primalObj a x ≤ worth a univ univ) ∧
    ∃ x : M → N → ℝ, PrimalFeasible x ∧ (∀ i j, x i j = 0 ∨ x i j = 1) ∧
      primalObj a x = worth a univ univ := by sorry

end AssignmentGame.CoreLP
