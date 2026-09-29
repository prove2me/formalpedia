-- Prove2me | Theorems.Thm_DoubleComplex_nonempty_HTot_transpose_equiv
-- name    : DoubleComplex.nonempty_HTot_transpose_equiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/37cad116-1956-58eb-a9c8-1147d4a5b73d
-- title:
--   Transposing a bounded double complex preserves total cohomology
-- statement:
--   Let $R$ be a commutative ring and let $D$ be a bounded double complex of $R$-modules in the sense of the structure [`DoubleComplex.Bounded`](def/AlgebraicGeometry_DoubleComplex.html#L11): modules $C^{p,q}$ for $p,q \in \mathbb{N}$, $R$-linear horizontal differentials $d_H \colon C^{p,q} \to C^{p+1,q}$ and vertical differentials $d_V \colon C^{p,q} \to C^{p,q+1}$ with $d_H^2 = 0$, $d_V^2 = 0$ and $d_V d_H = d_H d_V$ (commuting, not anticommuting), together with a bound $N$ such that $C^{p,q}$ is subsingleton whenever $N \le p$ or $N \le q$. Write $\mathrm{Tot}\,D$ for the associated total complex, whose differential in degree $n$ has components $d_H + (-1)^p d_V$, and $\mathrm{HTot}\,D\,n$ for its $n$-th cohomology, namely the quotient of $\ker d^n_{\mathrm{Tot}}$ by the submodule [`DoubleComplex.HTotB`](def/AlgebraicGeometry_DoubleComplex.html#L60), which is $\bot$ for $n = 0$ and otherwise the part of $\ker d^n_{\mathrm{Tot}}$ lying in the image of $d^{n-1}_{\mathrm{Tot}}$. Let $D^{t}$ be the transpose, with $(D^{t})^{a,b} = C^{b,a}$ and the two differentials exchanged. Then for every natural number $n$ the type of $R$-linear equivalences $\mathrm{HTot}\,D^{t}\,n \simeq \mathrm{HTot}\,D\,n$ is nonempty; the assertion is existence of an isomorphism, no particular one being named.
--
--   This is the standard symmetry of the total complex of a double complex under interchanging rows and columns, in the bounded first-quadrant setting used in the project. It lets statements about rows be deduced from the corresponding statements about columns, and is used in the treatment of the iterated Čech complex, in particular in [`AlgebraicGeometry.OModulePresheaf.iterCech_cols_exact_of_isQuasicoherent`](thm.html#AlgebraicGeometry.OModulePresheaf.iterCech_cols_exact_of_isQuasicoherent), in the comparison [`AlgebraicGeometry.OModulePresheaf.nonempty_HTot_biCech_equiv_prodCover_of_isQuasicoherent`](thm.html#AlgebraicGeometry.OModulePresheaf.nonempty_HTot_biCech_equiv_prodCover_of_isQuasicoherent) of the bi-Čech complex with the Čech complex of the product cover, and in [`DoubleComplex.finite_HTot_and_sum_finrank_HTot_eq_sum_finrank_colH`](thm.html#DoubleComplex.finite_HTot_and_sum_finrank_HTot_eq_sum_finrank_colH).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DoubleComplex_nonempty_HTot_transpose_equiv.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem DoubleComplex.nonempty_HTot_transpose_equiv
    {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R) (n : ℕ) :
    Nonempty (DoubleComplex.HTot (DoubleComplex.transpose D) n ≃ₗ[R] DoubleComplex.HTot D n) := by sorry
