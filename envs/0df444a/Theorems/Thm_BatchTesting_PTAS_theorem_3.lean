-- Prove2me | Theorems.Thm_BatchTesting_PTAS_theorem_3
-- name    : BatchTesting.PTAS.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:46.860228+00:00
-- url     : https://prove2.me/theorems/55eddd17-ae2b-4f25-b126-351989a3011b
-- title:
--   Theorem 3, p. 17 — $\mathrm{OPT}_F\le\mathrm{OPT}_{F_{\mathrm{great}}}\le K(\epsilon)\,\mathrm{OPT}_F$, $K(\epsilon)=(1+3\epsilon)(1+\epsilon)^2+2\epsilon(1+\epsilon)^4$
-- statement:
--   Let $(p,c,\beta)$ be an instance with $n\ge1$, $p_i\in[0,1]$, $c_i>0$, $\beta\ge0$, and let $0<\epsilon\le1$. Then
--
--   1. every path of the dynamic program over the great-looking states $F_{\mathrm{great}}$ is a path over $F$; and
--   2. for every path $\pi$ over $F$ there is a path $\pi'$ over $F_{\mathrm{great}}$ with
--   $$\mathrm{cost}(\pi')\ \le\ K(\epsilon)\cdot\mathrm{cost}(\pi),\qquad K(\epsilon)=(1+3\epsilon)(1+\epsilon)^2+2\epsilon(1+\epsilon)^4.$$
--
--   This is $\mathrm{OPT}_{F_{\mathrm{great}}}(N^{(\mathrm{none})})=(1+O(\epsilon))\cdot\mathrm{OPT}_F(N^{(\mathrm{none})})$: part 1 gives $\ge\mathrm{OPT}_F$, part 2 gives $\le K(\epsilon)\,\mathrm{OPT}_F$. Since there are only polynomially many great-looking states, this is the core of the PTAS.
--
--   **Formalization Note.** The paper's $1+O(\epsilon)$ is replaced by the explicit constant of its own chain on pp. 19–20: $(1+3\epsilon)(1+\epsilon)^2\,\mathrm{OPT}_F+2\epsilon(1+\epsilon)^2\cdot(1+\epsilon)^2\,\mathrm{OPT}_F$. $\epsilon\le1$ is added (used by Property A and inequality (12)).
-- source:
--   Segev & Shaposhnik, A Polynomial-Time Approximation Scheme for Sequential Batch Testing of Series Systems, SSRN preprint 3277805 (Nov. 2018), p. 17, §4.2, Theorem 3 (proof pp. 17–24; explicit chain pp. 19–20)

import Mathlib
import Definitions.Def_BatchTesting_PTAS_Model

namespace BatchTesting.PTAS

theorem theorem_3 {n : ℕ} (I : Instance n) (hI : I.Standing) (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1) :
    (∀ π, IsPath I eps (FGreat I eps) π → IsPath I eps (F I eps) π) ∧
      ∀ π, IsPath I eps (F I eps) π →
        ∃ π', IsPath I eps (FGreat I eps) π' ∧ pathCost I eps π' ≤ K eps * pathCost I eps π := by sorry

end BatchTesting.PTAS
