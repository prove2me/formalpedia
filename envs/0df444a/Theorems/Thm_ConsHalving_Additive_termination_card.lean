-- Prove2me | Theorems.Thm_ConsHalving_Additive_termination_card
-- name    : ConsHalving.Additive.termination_card
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:40.133179+00:00
-- url     : https://prove2.me/theorems/3b2be9af-a552-4db0-b802-439039a26bf8
-- title:
--   Proof of Theorem 2.2, p. 5 — if x is the unique solution of S ∪ T then |T| ≥ m − n
-- statement:
--   Let $n$ agents have additive utilities $u_i(j)$ over $m$ items, let $T$ be a set of items, and let $x$ solve the system $S$: $\sum_j(x_j-\tfrac12)u_i(j)=0$ for every agent $i$. If $x$ is the only solution of $S\cup T$, that is, every $y$ with $\sum_j(y_j-\tfrac12)u_i(j)=0$ for all $i$ and $y_j=x_j$ for all $j\in T$ equals $x$, then
--   $$|T|\ \ge\ m-n .$$
--
--   This is the termination step of the algorithm: when the loop stops, the $n+|T|$ equations of $S\cup T$ pin down a unique point, so at most $n$ items are left outside $T$, and hence at most $n$ items are cut.
--
--   **Formalization Note** The inequality is written $m\le n+|T|$ to avoid truncated subtraction of natural numbers. The hypothesis that $x$ itself solves $S$ is part of the paper's situation ($x$ is the unique solution) and is needed: without it the uniqueness hypothesis could hold vacuously for an infeasible system.
-- source:
--   Goldberg et al., Consensus Halving for Sets of Items, arXiv:2007.06754v1, p. 5, proof of Theorem 2.2, last paragraph

import Mathlib
import Definitions.Def_ConsHalving_Additive_Setting

namespace ConsHalving.Additive

theorem termination_card {n m : ℕ} (u : Fin n → Fin m → ℝ) (T : Finset (Fin m))
    (x : Fin m → ℝ) (hx : SolvesS u x) (huniq : ∀ y, SolvesST u T x y → y = x) :
    m ≤ n + T.card := by sorry

end ConsHalving.Additive
