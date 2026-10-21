-- Prove2me | Theorems.Thm_BatchTesting_PTAS_greedy_within_class
-- name    : BatchTesting.PTAS.greedy_within_class
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:39.048565+00:00
-- url     : https://prove2.me/theorems/69da7431-68b3-4ef9-af16-0141fa19996d
-- title:
--   §2.1–2.2, pp. 8–10 — greedy-within-class: every testing scheme is matched by a path of the DP over $F$
-- statement:
--   Let $(p,c,\beta)$ be an instance with $n\ge1$, $p_i\in[0,1]$, $c_i>0$, $\beta\ge0$, and let $0<\epsilon\le1$. For every testing scheme $S$ there is a path $0=N^{(0)}\to\cdots\to N^{(T)}=N^{(\mathrm{all})}$ of the dynamic program over the full state space $F$ whose cost, converted back to the original units, is at most the expected cost of $S$ under the rounded costs $\hat c$:
--
--   $$c_{\min}\cdot\sum_{t=1}^{T}P_0(N^{(t-1)})\,C(N^{(t)}-N^{(t-1)})\ \le\ E_{\hat c}(S).$$
--
--   This is the content of the greedy-within-class property: testing the variables of each cost class in non-decreasing order of $p_i$ never hurts, so a scheme is determined, up to cost, by how many variables of each class it has tested. It shows $c_{\min}\cdot\mathrm{OPT}_F(N^{(\mathrm{none})})$ is at most the rounded optimum.
--
--   **Formalization Note.** The page says an optimal scheme "necessarily" has the property; with ties among the $p_i$ that is true only up to ties, so the statement is the dominance form the dynamic program needs. Empty batches of $S$ (which would be zero actions) are allowed in $S$; the path has strictly increasing states.
-- source:
--   Segev & Shaposhnik, A Polynomial-Time Approximation Scheme for Sequential Batch Testing of Series Systems, SSRN preprint 3277805 (Nov. 2018), pp. 8–9, §2.1 (The greedy-within-class property), and p. 10, §2.2, eq. (1)

import Mathlib
import Definitions.Def_BatchTesting_PTAS_Model

namespace BatchTesting.PTAS

theorem greedy_within_class {n : ℕ} (I : Instance n) (hI : I.Standing) (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1)
    (S : List (Finset (Fin n))) (hS : IsTestingScheme S) :
    ∃ π, IsPath I eps (F I eps) π ∧
      cmin I * pathCost I eps π ≤ expectedCostWith I (roundedCost I eps) S := by sorry

end BatchTesting.PTAS
