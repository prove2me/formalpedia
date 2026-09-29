-- Prove2me | Theorems.Thm_DoubleComplex_finite_HTot_and_sum_finrank_HTot_eq_sum_finrank_colH
-- name    : DoubleComplex.finite_HTot_and_sum_finrank_HTot_eq_sum_finrank_colH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/95970f0a-451b-52e0-85f3-46e95c225c03
-- title:
--   Euler characteristic of a bounded double complex via columns
-- statement:
--   Let $k$ be a field and let $D$ be a bounded double complex of $k$-vector spaces in the sense of [`DoubleComplex.Bounded k`](def/AlgebraicGeometry_DoubleComplex.html#L11): spaces $C^{p,q}$ indexed by $p,q\in\mathbb{N}$, $k$-linear horizontal maps $d_H^{p,q}\colon C^{p,q}\to C^{p+1,q}$ and vertical maps $d_V^{p,q}\colon C^{p,q}\to C^{p,q+1}$ with $d_H\circ d_H=0$, $d_V\circ d_V=0$ and $d_V\circ d_H=d_H\circ d_V$ (strictly commuting, not anticommuting), together with a bound $N\in\mathbb{N}$ such that $C^{p,q}$ is a subsingleton whenever $N\le p$ or $N\le q$. Assume that for all $p,q$ the column cohomology $\mathrm{colH}\,D\,p\,q$ — the quotient of $\ker d_V^{p,q}$ by $\bot$ for $q=0$, and by the preimage of $\operatorname{im} d_V^{p,q-1}$ for $q>0$ — is a finite $k$-module. The conclusion is twofold: first, for every $n$ the total cohomology $\mathrm{HTot}\,D\,n$, formed in the same way from the total differential $d_{\mathrm{Tot}}=d_H+(-1)^p d_V$, is finite over $k$; second, $$\sum_{n=0}^{2N-1}(-1)^n\dim_k \mathrm{HTot}\,D\,n=\sum_{p=0}^{N-1}\sum_{q=0}^{N-1}(-1)^{p+q}\dim_k \mathrm{colH}\,D\,p\,q.$$
--
--   This is the statement that the Euler characteristic of the total complex of a bounded double complex equals the alternating sum of the dimensions of its column cohomologies, the counting consequence of the spectral sequence of a double complex; the entries $C^{p,q}$ themselves need not be finite-dimensional. It is used in the computation of the Euler characteristic of a Mumford bundle twisted by a pullback, in [`AlgebraicGeometry.Polarisation.eulerChar_mumfordBundle_tensor_pullback_snd_eq_sum_alternating_length_of_forall_mem`](thm.html#AlgebraicGeometry.Polarisation.eulerChar_mumfordBundle_tensor_pullback_snd_eq_sum_alternating_length_of_forall_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DoubleComplex_finite_HTot_and_sum_finrank_HTot_eq_sum_finrank_colH.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem DoubleComplex.finite_HTot_and_sum_finrank_HTot_eq_sum_finrank_colH
    {k : Type u} [Field k] (D : DoubleComplex.Bounded k)
    (hcol : ∀ p q : ℕ, Module.Finite k (DoubleComplex.colH D p q)) :
    (∀ n : ℕ, Module.Finite k (DoubleComplex.HTot D n)) ∧
      ∑ n ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ n * (Module.finrank k (DoubleComplex.HTot D n) : ℤ) =
        ∑ p ∈ Finset.range D.N, ∑ q ∈ Finset.range D.N,
          (-1 : ℤ) ^ (p + q) * (Module.finrank k (DoubleComplex.colH D p q) : ℤ) := by sorry
