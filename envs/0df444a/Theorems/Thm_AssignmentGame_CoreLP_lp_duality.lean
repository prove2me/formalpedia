-- Prove2me | Theorems.Thm_AssignmentGame_CoreLP_lp_duality
-- name    : AssignmentGame.CoreLP.lp_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:15:33.497135+00:00
-- url     : https://prove2.me/theorems/fc16dda3-58ab-4fe2-9154-3886e465c821
-- title:
--   Sec. 3.1 (quoting Dantzig) — duality for the assignment LP: $w_{\min} = z_{\max}$
-- statement:
--   Let $M$ and $N$ be finite sets and $a = (a_{ij})$ a matrix with $a_{ij} \ge 0$. Consider the primal assignment LP (3.1)–(3.2), maximise $z(x) = \sum_{i,j} a_{ij}x_{ij}$ subject to $x_{ij} \ge 0$, $\sum_i x_{ij} \le 1$, $\sum_j x_{ij} \le 1$, and its dual (3.3)–(3.4), minimise $w(u,v) = \sum_i u_i + \sum_j v_j$ subject to $u_i \ge 0$, $v_j \ge 0$, $u_i + v_j \ge a_{ij}$. Then
--
--   1. (weak duality) $z(x) \le w(u, v)$ for every primal-feasible $x$ and every dual-feasible $(u, v)$; and
--   2. (strong duality) there are a primal-feasible $x$ and a dual-feasible $(u,v)$ with $z(x) = w(u,v)$.
--
--   Equivalently, both optima exist and
--   $$w_{\min} = z_{\max}.$$
--   The paper quotes this from the fundamental duality theorem of linear programming (Dantzig, p. 129), noting that both programs are feasible by inspection.
-- source:
--   Shapley and Shubik, The Assignment Game I: The Core, Int. J. Game Theory 1 (1971), p. 118, Sec. 3.1, after Eq. (3.4), and footnote 1 (quoting Dantzig, Linear Programming and Extensions, p. 129)

import Mathlib
import Definitions.Def_AssignmentGame_CoreLP_Game

open Finset

namespace AssignmentGame.CoreLP

theorem lp_duality {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    (∀ (x : M → N → ℝ) (p : (M → ℝ) × (N → ℝ)), PrimalFeasible x → DualFeasible a p →
      primalObj a x ≤ dualObj p) ∧
    ∃ (x : M → N → ℝ) (p : (M → ℝ) × (N → ℝ)), PrimalFeasible x ∧ DualFeasible a p ∧
      primalObj a x = dualObj p := by sorry

end AssignmentGame.CoreLP
