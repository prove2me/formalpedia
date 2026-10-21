-- Prove2me | Theorems.Thm_BatchTesting_PTAS_theorem_2
-- name    : BatchTesting.PTAS.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:57.367546+00:00
-- url     : https://prove2.me/theorems/98e314eb-764c-4cf5-b81f-47a233dc4bba
-- title:
--   Theorem 2, p. 12 — $\mathrm{OPT}_{F_{\mathrm{nice}}}(N^{(\mathrm{none})})\le(1+\epsilon)\cdot\mathrm{OPT}_F(N^{(\mathrm{none})})$
-- statement:
--   Let $(p,c,\beta)$ be an instance with $n\ge1$, $p_i\in[0,1]$, $c_i>0$, $\beta\ge0$, and let $0<\epsilon\le1$. For every path $\pi$ of the dynamic program over the full state space $F$ there is a path $\pi'$ all of whose states are nice-looking, with
--
--   $$\mathrm{cost}(\pi')\ \le\ (1+\epsilon)\cdot\mathrm{cost}(\pi).$$
--
--   Equivalently, $\mathrm{OPT}_{F_{\mathrm{nice}}}(N^{(\mathrm{none})})\le(1+\epsilon)\cdot\mathrm{OPT}_F(N^{(\mathrm{none})})$: restricting the dynamic program to nice-looking states, where every class at least $\kappa=\lceil\log_{1+\epsilon}(n/\epsilon)\rceil$ below the top touched class is exhausted, loses a factor of at most $1+\epsilon$. This yields the paper's quasi-PTAS and is the first step of Theorem 3.
--
--   **Formalization Note.** Stated in path form (an existence statement for every $F$-path) rather than with infima over paths, so it is never vacuous.
-- source:
--   Segev & Shaposhnik, A Polynomial-Time Approximation Scheme for Sequential Batch Testing of Series Systems, SSRN preprint 3277805 (Nov. 2018), p. 12, §3.3, Theorem 2 (proof §3.4, pp. 12–14)

import Mathlib
import Definitions.Def_BatchTesting_PTAS_Model

namespace BatchTesting.PTAS

theorem theorem_2 {n : ℕ} (I : Instance n) (hI : I.Standing) (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1)
    (π : List (State I eps)) (hπ : IsPath I eps (F I eps) π) :
    ∃ π', IsPath I eps (FNice I eps) π' ∧ pathCost I eps π' ≤ (1 + eps) * pathCost I eps π := by sorry

end BatchTesting.PTAS
