-- Prove2me | Theorems.Thm_DoubleComplex_finite_HTot_and_sum_finrank_HTot_eq_sub_of_rowShift
-- name    : DoubleComplex.finite_HTot_and_sum_finrank_HTot_eq_sub_of_rowShift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/aab5c967-d8a0-5951-a615-40920c18fe1d
-- title:
--   Peeling off the bottom row of a bounded double complex
-- statement:
--   Let $k$ be a field and let $D$ be a bounded double complex of $k$-vector spaces in the sense of [`DoubleComplex.Bounded k`](def/AlgebraicGeometry_DoubleComplex.html#L11): modules $C^{p,q}$ indexed by $p,q \in \mathbb{N}$, horizontal maps $d_H \colon C^{p,q} \to C^{p+1,q}$ and vertical maps $d_V \colon C^{p,q} \to C^{p,q+1}$ with $d_H^2 = 0$, $d_V^2 = 0$ and $d_V \circ d_H = d_H \circ d_V$, together with a bound $N$ such that $C^{p,q}$ is a subsingleton whenever $N \le p$ or $N \le q$. Write $D^{\uparrow}$ for the shifted double complex with $(D^{\uparrow})^{p,q} = C^{p,q+1}$, the same differentials and the same bound $N$, and write $H^n(\mathrm{Tot}\,D)$ for [`DoubleComplex.HTot`](def/AlgebraicGeometry_DoubleComplex.html#L65), the cohomology of the total complex with differential $d_H + (-1)^p d_V$. Assume that every $H^n(\mathrm{Tot}\,D^{\uparrow})$ is finite-dimensional over $k$, and that every $k$-space [`DoubleComplex.colH (DoubleComplex.transpose D) 0 p`](def/AlgebraicGeometry_DoubleComplex.html#L140), i.e. the $p$-th cohomology $\ker(d_H \colon C^{p,0} \to C^{p+1,0})$ modulo the image of $d_H \colon C^{p-1,0} \to C^{p,0}$ (with $\bot$ in place of the image when $p = 0$) of the bottom row, is finite-dimensional. Then every $H^n(\mathrm{Tot}\,D)$ is finite-dimensional and, as an identity in $\mathbb{Z}$, $$\sum_{n < 2N} (-1)^n \dim_k H^n(\mathrm{Tot}\,D) = \sum_{p < 2N} (-1)^p \dim_k H^p(C^{\bullet,0}) - \sum_{n < 2N} (-1)^n \dim_k H^n(\mathrm{Tot}\,D^{\uparrow}).$$
--
--   This is the inductive step in the computation of the Euler characteristic of the total complex of a bounded double complex: the bottom row is split off from $\mathrm{Tot}\,D$, leaving the total complex of the rows $q \ge 1$, and the alternating dimension sums add up accordingly. It is used by [`DoubleComplex.finite_HTot_and_sum_finrank_HTot_eq_sum_finrank_colH`](thm.html#DoubleComplex.finite_HTot_and_sum_finrank_HTot_eq_sum_finrank_colH), which iterates the step to express the Euler characteristic of $\mathrm{Tot}\,D$ as the sum of those of the rows; the finiteness and dimension bookkeeping comes from the three-term exactness lemma [`LinearMap.finite_and_sum_finrank_eq_of_exact_of_exact_of_exact`](thm.html#LinearMap.finite_and_sum_finrank_eq_of_exact_of_exact_of_exact).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DoubleComplex_finite_HTot_and_sum_finrank_HTot_eq_sub_of_rowShift.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem DoubleComplex.finite_HTot_and_sum_finrank_HTot_eq_sub_of_rowShift
    {k : Type u} [Field k] (D : DoubleComplex.Bounded k)
    (hup : ∀ n : ℕ, Module.Finite k (DoubleComplex.HTot
        ({ C := fun p q => D.C p (q + 1), dH := fun p q => D.dH p (q + 1), dV := fun p q => D.dV p (q + 1),
                dH_sq := fun p q => D.dH_sq p (q + 1), dV_sq := fun p q => D.dV_sq p (q + 1),
                dHV_comm := fun p q => D.dHV_comm p (q + 1), N := D.N,
                hBound := fun p q h => D.hBound p (q + 1) (h.imp id Nat.le_succ_of_le) } : DoubleComplex.Bounded k) n))
    (hrow : ∀ p : ℕ, Module.Finite k (DoubleComplex.colH (DoubleComplex.transpose D) 0 p)) :
    (∀ n : ℕ, Module.Finite k (DoubleComplex.HTot D n)) ∧
      ∑ n ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ n * (Module.finrank k (DoubleComplex.HTot D n) : ℤ) =
        ∑ p ∈ Finset.range (2 * D.N),
            (-1 : ℤ) ^ p * (Module.finrank k (DoubleComplex.colH (DoubleComplex.transpose D) 0 p) : ℤ) -
          ∑ n ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ n * (Module.finrank k (DoubleComplex.HTot
            ({ C := fun p q => D.C p (q + 1), dH := fun p q => D.dH p (q + 1), dV := fun p q => D.dV p (q + 1),
                dH_sq := fun p q => D.dH_sq p (q + 1), dV_sq := fun p q => D.dV_sq p (q + 1),
                dHV_comm := fun p q => D.dHV_comm p (q + 1), N := D.N,
                hBound := fun p q h => D.hBound p (q + 1) (h.imp id Nat.le_succ_of_le) } : DoubleComplex.Bounded k) n) : ℤ) := by sorry
