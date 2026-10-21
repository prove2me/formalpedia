-- Prove2me | Theorems.Thm_BatchTesting_PTAS_rounding_sandwich
-- name    : BatchTesting.PTAS.rounding_sandwich
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:39.205529+00:00
-- url     : https://prove2.me/theorems/6688380c-e2de-4561-afdf-2765ed2cddcc
-- title:
--   §2.1, p. 8 — rounding the costs up to powers of $1+\epsilon$ changes every expected cost by a factor in $[1,1+\epsilon]$
-- statement:
--   Let $(p,c,\beta)$ be an instance of sequential batch testing on $n\ge1$ variables with $p_i\in[0,1]$, $c_i>0$ and $\beta\ge0$, and let $0<\epsilon\le1$. Let $\hat c_i=c_{\min}(1+\epsilon)^{r_i}$ be the cost $c_i$ rounded up: $c_i/c_{\min}$ is replaced by the nearest power of $1+\epsilon$ at or above it. Write $E_c(S)$ for the expected cost of a testing scheme $S$ under individual costs $c$. Then for every testing scheme $S$,
--
--   $$E_c(S)\ \le\ E_{\hat c}(S)\ \le\ (1+\epsilon)\,E_c(S).$$
--
--   This is the first step of the algorithm: after rounding, the optimal expected cost grows by a factor of at most $1+\epsilon$, and the variables fall into $R+1$ cost classes of identical cost.
--
--   **Formalization Note.** The rounded costs are in the original units ($c_{\min}$ times a power of $1+\epsilon$), so both sides compare the same set-up cost $\beta$. $\beta\ge0$ and $p_i\ge0$ are used; $\epsilon\le1$ is a mission-wide hypothesis, not needed here.
-- source:
--   Segev & Shaposhnik, A Polynomial-Time Approximation Scheme for Sequential Batch Testing of Series Systems, SSRN preprint 3277805 (Nov. 2018), p. 8, §2.1 (Creating cost classes)

import Mathlib
import Definitions.Def_BatchTesting_PTAS_Model

namespace BatchTesting.PTAS

theorem rounding_sandwich {n : ℕ} (I : Instance n) (hI : I.Standing) (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1)
    (S : List (Finset (Fin n))) (hS : IsTestingScheme S) :
    expectedCost I S ≤ expectedCostWith I (roundedCost I eps) S ∧
      expectedCostWith I (roundedCost I eps) S ≤ (1 + eps) * expectedCost I S := by sorry

end BatchTesting.PTAS
