-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_coefficientIn_coeff
-- name    : ApproxPolySatCH.Main.coefficientIn_coeff
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:56:14.491177+00:00
-- url     : https://prove2.me/theorems/8a87e62e-c454-47fb-8339-0bfcbda294dc
-- title:
--   Coefficient formula for extracting a fixed variable exponent
-- statement:
--   Let $A$ be a commutative ring, let $p\in A[X_0,\ldots,X_{n-1}]$, and fix a variable $v$ and exponent $j$. Write $p_j$ for the polynomial obtained by taking the coefficient of $X_v^j$ while leaving the other variables in place. For every exponent vector $d$,
--   $$[X^d]p_j=
--   \begin{cases}
--   [X^{d+j\mathbf e_v}]p,&d_v=0,\\
--   0,&d_v\ne0.
--   \end{cases}$$
--   In particular, $p_j$ is supported entirely in the hyperplane $d_v=0$, and its coefficients there are exactly the coefficients of $p$ at exponent $j$ in $X_v$.
--
--   This is the direct coefficient description of the trailing-coefficient interface used in Lemma 12. It also makes clear that extraction cannot create cancellation or change a coefficient once the fixed exponent $j$ has been chosen.
--
--   **Formalization Note.** Exponent-vector subtraction in the definition is truncated natural-number subtraction on `Finsupp`; the proof uses `Finsupp.tsub_apply`, together with `e_v=j` to recover $e=(e-j\mathbf e_v)+j\mathbf e_v$.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), definition of $\operatorname{TT}_U$ and coefficient extraction, p.12; used in the proof of Lemma 12, p.22, equation (22); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=12

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

theorem ApproxPolySatCH.Main.coefficientIn_coeff {A : Type} [CommRing A] {n : ℕ}
    (v : Fin n) (j : ℕ) (p : Poly A n) (d : Fin n →₀ ℕ) :
    (coefficientIn v j p).coeff d =
      if d v = 0 then p.coeff (d + Finsupp.single v j) else 0 := by sorry
