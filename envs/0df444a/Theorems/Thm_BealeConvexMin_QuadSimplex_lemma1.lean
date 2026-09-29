-- Prove2me | Theorems.Thm_BealeConvexMin_QuadSimplex_lemma1
-- name    : BealeConvexMin.QuadSimplex.lemma1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:33:03.793367+00:00
-- url     : https://prove2.me/theorems/e01ff94e-5579-4379-8de1-4257eeac23ad
-- title:
--   Lemma 1 — a free variable enters with no cross terms
-- statement:
--   Let $(c_{kl})_{k,l=0}^{N}$ be symmetric with $c_{pp}\neq0$, and let the new nonbasic variable be the free variable of (3.2),
--   $$u_r=c_{p0}+\sum_{l=1}^{N}c_{pl}z_l,$$
--   i.e. the coefficients of (3.3) are $d_l=c_{pl}$ for $l=0,\dots,N$. Then (3.4) gives
--   $$e_q=\frac1{c_{pp}},\qquad e_l=-\frac{c_{pl}}{c_{pp}}\quad(l\neq q),$$
--   and every off-diagonal entry of the new row and column vanishes:
--   $$c''_{ql}=c''_{kq}=0\qquad\text{for }k,l\neq q .$$
--
--   Since the index $0$ is included, $C$ contains no linear term in the new free variable after the pivot. This is the first half of Beale's termination argument.
--
--   **Formalization Note** The new variable is stored in slot $p$, so $q$ is $p$ and "$k,l\neq q$" reads "$k,l\neq p$", index $0$ included. The hypothesis $c_{pp}\neq0$ is the paper's $d_{qp}\neq0$ of (3.3); in the iteration a free variable enters only when $c_{pp}>0$.
-- source:
--   Beale, On Minimizing a Convex Function Subject to Linear Inequalities, J. R. Statist. Soc. B 17(2), 1955, https://doi.org/10.1111/j.2517-6161.1955.tb00191.x, p. 177 (PDF p. 5), Lemma 1

import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC

namespace BealeConvexMin.QuadSimplex

/-- Beale (1955), §3, p. 177, Lemma 1. If the new nonbasic variable is the free variable
`u_r = c_p0 + Σ_l c_pl z_l` of (3.2), i.e. (3.3) has coefficients `d = (c_p0, c_p1, …, c_pN)`
(row `p` of `c`), then `e_q = 1/c_pp`, `e_l = -c_pl/c_pp` for `l ≠ q`, and every off-diagonal entry
of the new row and column (slot `p`, where the paper's `z_q` is stored) vanishes, index `0`
included: `c''_ql = c''_kq = 0` for `k, l ≠ q`. `(c_kl)` is symmetric and `c_pp ≠ 0`. -/
theorem lemma1 {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hc : c.IsSymm)
    (p : Fin (N + 1)) (hp : c p p ≠ 0) :
    pivotE (c p) p p = 1 / c p p ∧
    (∀ l, l ≠ p → pivotE (c p) p l = -c p l / c p p) ∧
    ∀ k, k ≠ p → pivotC c p (c p) p k = 0 ∧ pivotC c p (c p) k p = 0 := by sorry

end BealeConvexMin.QuadSimplex
