-- Prove2me | Theorems.Thm_BatchTesting_PTAS_pathCost_eq_expectedCost
-- name    : BatchTesting.PTAS.pathCost_eq_expectedCost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:44.570006+00:00
-- url     : https://prove2.me/theorems/526cb35d-4648-4062-96f4-7b327263b853
-- title:
--   §2.2, p. 10 and eq. (3), p. 13 — the scheme read off a DP path is a testing scheme whose rounded expected cost is the path cost
-- statement:
--   Let $(p,c,\beta)$ be an instance with $n\ge1$, $p_i\in[0,1]$, $c_i>0$, $\beta\ge0$, let $0<\epsilon\le1$, and let $G\subseteq F$ be any set of states. Let $0=N^{(0)}\to\cdots\to N^{(T)}=N^{(\mathrm{all})}$ be a $G$-path, and let $S$ be its testing scheme, whose $t$-th batch is $\biguplus_r C_r[N^{(t-1)}_r+1,N^{(t)}_r]$. Then $S$ is a testing scheme of $[n]$, and its expected cost under the rounded costs $\hat c$ is
--
--   $$E_{\hat c}(S)\ =\ c_{\min}\cdot\sum_{t=1}^{T}P_0(N^{(t-1)})\cdot C(N^{(t)}-N^{(t-1)}).$$
--
--   This is the path form (3) of the recursion (1)–(2): the value of the dynamic program on any restricted state space is the expected cost of an actual testing scheme, which is how the algorithm turns its optimal path into its output.
--
--   **Formalization Note.** The factor $c_{\min}$ converts the normalized units of $C(\Delta)$ (p. 8) back to the original units.
-- source:
--   Segev & Shaposhnik, A Polynomial-Time Approximation Scheme for Sequential Batch Testing of Series Systems, SSRN preprint 3277805 (Nov. 2018), p. 10, §2.2, eq. (1); p. 11, eq. (2); p. 13, eq. (3)

import Mathlib
import Definitions.Def_BatchTesting_PTAS_Model

namespace BatchTesting.PTAS

theorem pathCost_eq_expectedCost {n : ℕ} (I : Instance n) (hI : I.Standing) (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1)
    (G : Finset (State I eps)) (hG : G ⊆ F I eps) (π : List (State I eps)) (hπ : IsPath I eps G π) :
    IsTestingScheme (schemeOf I eps π) ∧
      expectedCostWith I (roundedCost I eps) (schemeOf I eps π) = cmin I * pathCost I eps π := by sorry

end BatchTesting.PTAS
