-- Prove2me | Theorems.Thm_EvenCycleTuran_BipC6C8_lower_bound
-- name    : EvenCycleTuran.BipC6C8.lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:31.097802+00:00
-- url     : https://prove2.me/theorems/7fdaae7f-4519-424a-83c7-03b37e6fca6f
-- title:
--   Theorem 10's construction (p. 9) with k = 4, l = 3 — K_{3,n−3} is bipartite, C₈-free and has 6·C(n−3, 3) six-cycles
-- statement:
--   Let $n\ge 3$ and let $K_{3,n-3}$ be the complete bipartite graph with classes of sizes $3$ and $n-3$. Then $K_{3,n-3}$ is bipartite, contains no cycle of length $8$, and the number of $6$-cycles in it is
--   $$\mathcal N(C_6,K_{3,n-3}) = 6\binom{n-3}{3}=(n-3)(n-4)(n-5).$$
--
--   This is the lower bound $\mathrm{ex}_{bip}(n,C_6,C_8)\ge n^3-O(n^2)$ in Theorem 12: it is Theorem 10's construction $K_{k-1,n-k+1}$ with $k=4$, $l=3$, which is bipartite (Remark 2).
--
--   **Formalization Note** $\mathcal N$ counts unlabelled copies (subgraphs isomorphic to $C_6$). $n-3$ is natural-number subtraction, nonnegative under $n\ge 3$.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 9, proof of Theorem 10, first paragraph (k = 4, l = 3); p. 11, Remark 2 ("the construction given in Theorem 10 is bipartite")

import Mathlib
import Definitions.Def_EvenCycleTuran_BipC6C8_Setting
open Finset SimpleGraph Filter Asymptotics

namespace EvenCycleTuran.BipC6C8

theorem lower_bound (n : ℕ) (hn : 3 ≤ n) :
    (bipGraph n 3).Colorable 2 ∧ EvenCycleTuran.C4Count.CycleFree {8} (bipGraph n 3) ∧
      (bipGraph n 3).copyCount (cycleGraph 6) = 6 * (n - 3).choose 3 := by sorry

end EvenCycleTuran.BipC6C8
