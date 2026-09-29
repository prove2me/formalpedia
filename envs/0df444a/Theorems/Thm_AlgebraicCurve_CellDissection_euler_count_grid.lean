-- Prove2me | Theorems.Thm_AlgebraicCurve_CellDissection_euler_count_grid
-- name    : AlgebraicCurve.CellDissection.euler_count_grid
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/d1918b8c-11a0-5cfc-84c7-372953c9b2ee
-- title:
--   Euler count of a grid dissection of an n-sheeted cover
-- statement:
--   Let $n$, $J$, $K$, $n_p$, $n_c$ be natural numbers and $g$ an integer, with $n_p + n_c = J\cdot K$. Let $\iota_c$ be a finite type with $\#\iota_c = n_c$, let $b \mapsto \mathrm{fib}\,b$ assign a finite type to each $b \in \iota_c$, and let $e_c$ assign to each $b$ and each $w \in \mathrm{fib}\,b$ a natural number, subject to $\sum_{w} e_c(b,w) = n$ for every $b$. Let $\iota_p$ be a finite type and $e_p : \iota_p \to \mathbb{N}$ with $\sum_{q} e_p(q) = n$. Assume the Riemann–Hurwitz identity $$\Big(\sum_{b}\sum_{w}\big(e_c(b,w)-1\big)\Big) + \sum_{q}\big(e_p(q)-1\big) = 2g-2+2n$$ in $\mathbb{Z}$. Then $$2\,n\big((J+1)(K+1)+JK+K\big) - \Big(6nn_p + \sum_b\sum_w 6\,e_c(b,w) + \sum_q e_p(q)\,(2J+4K)\Big) + 2\Big(nn_p + \sum_b \#\mathrm{fib}\,b + \#\iota_p\Big) = 2(2-2g),$$ all terms being read as integers. The three groups of terms are twice the vertex count, the total side count, and twice the cell count of the intended dissection, but the assertion itself is a purely arithmetical identity among the stated data.
--
--   This is the combinatorial Euler-characteristic bookkeeping for a grid dissection of an $n$-sheeted branched cover of the sphere: a $J \times K$ array of squares carries $n$ hexagonal cells over each of the $n_p$ unbranched squares, one cell with $6\,e_c(b,w)$ sides for each point $w$ of the fibre over each of the $n_c$ branched squares $b$, and one cell with $e_p(q)(2J+4K)$ sides for each point $q$ outside the rectangle, the vertices being $n$ copies of the $(J+1)(K+1)+JK+K$ grid vertices. It is a helper row for [`AlgebraicCurve.exists_pairedCellFamily`](thm.html#AlgebraicCurve.exists_pairedCellFamily), which invokes it at the grid construction to read off $2-2g$ from the cell data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CellDissection_euler_count_grid.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.CellDissection.euler_count_grid (n J K np nc : ℕ) (g : ℤ) (hJK : np + nc = J * K)
    (ιc : Type*) [Fintype ιc] (hnc : Fintype.card ιc = nc)
    (fib : ιc → Type*) [∀ b, Fintype (fib b)] (ec : ∀ b, fib b → ℕ)
    (hec : ∀ b, ∑ w, ec b w = n)
    (ιp : Type*) [Fintype ιp] (ep : ιp → ℕ) (hep : ∑ q, ep q = n)
    (hRH : (∑ b, ∑ w, ((ec b w : ℤ) - 1)) + ∑ q, ((ep q : ℤ) - 1) = 2 * g - 2 + 2 * (n : ℤ)) :
    2 * ((n : ℤ) * ((J + 1) * (K + 1) + J * K + K)) -
        ((6 * n * np : ℤ) + (∑ b, ∑ w, (6 * ec b w : ℤ)) + ∑ q, ((ep q : ℤ) * (2 * J + 4 * K))) +
        2 * ((n * np : ℤ) + (∑ b, (Fintype.card (fib b) : ℤ)) + Fintype.card ιp) =
      2 * (2 - 2 * g) := by sorry
