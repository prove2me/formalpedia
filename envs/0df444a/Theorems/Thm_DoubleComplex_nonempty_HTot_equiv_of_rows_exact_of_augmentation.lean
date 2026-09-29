-- Prove2me | Theorems.Thm_DoubleComplex_nonempty_HTot_equiv_of_rows_exact_of_augmentation
-- name    : DoubleComplex.nonempty_HTot_equiv_of_rows_exact_of_augmentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/1b8f8225-d6a4-5f58-b0e6-5b3e7f34e32d
-- title:
--   Augmented staircase lemma for bounded double complexes
-- statement:
--   Let $R$ be a commutative ring and let $D$ be a bounded double complex of $R$-modules in the sense of the project's structure [`DoubleComplex.Bounded`](def/AlgebraicGeometry_DoubleComplex.html#L11): modules $C^{p,q}$ indexed by $p,q\in\mathbb{N}$, horizontal maps $d_H^{p,q}\colon C^{p,q}\to C^{p+1,q}$ and vertical maps $d_V^{p,q}\colon C^{p,q}\to C^{p,q+1}$ with $d_H\circ d_H=0$, $d_V\circ d_V=0$, commuting squares $d_V^{p+1,q}\circ d_H^{p,q}=d_H^{p,q+1}\circ d_V^{p,q}$, and an integer $N$ with $C^{p,q}$ a subsingleton whenever $N\le p$ or $N\le q$. Let $A^m$ ($m\in\mathbb{N}$) be $R$-modules with $R$-linear maps $d_A^m\colon A^m\to A^{m+1}$ and $\varepsilon^m\colon A^m\to C^{0,m}$ such that each $\varepsilon^m$ is injective, $d_V^{0,m}\circ\varepsilon^m=\varepsilon^{m+1}\circ d_A^m$, $\ker d_H^{0,m}=\operatorname{im}\varepsilon^m$, and every row is exact to the right of the first column: $\ker d_H^{p+1,m}\subseteq\operatorname{im}d_H^{p,m}$ for all $p,m$. Writing $\mathrm{HTot}\,D\,n$ for the cohomology of the total complex, namely $\ker(d_{\mathrm{Tot}}^n)$ modulo $\bot$ for $n=0$ and modulo the preimage of $\operatorname{im}(d_{\mathrm{Tot}}^{n})$ in $\ker(d_{\mathrm{Tot}}^{n+1})$ in degree $n+1$, where $d_{\mathrm{Tot}}$ is assembled from $d_H$ and $d_V$ with the signs $(-1)^p$, the conclusion asserts the existence (as a `Nonempty` statement about the type of $R$-linear equivalences) of isomorphisms $\mathrm{HTot}\,D\,0\cong\ker d_A^0$ and, for every $n$, $\mathrm{HTot}\,D\,(n+1)\cong\ker d_A^{n+1}/\bigl(\operatorname{im}d_A^{n}\cap\ker d_A^{n+1}\bigr)$, the second quotient being formed as the preimage of $\operatorname{im}d_A^n$ under the inclusion of $\ker d_A^{n+1}$. No relation $d_A^{m+1}\circ d_A^m=0$ is assumed; it follows from the hypotheses, so the displayed quotients are the cohomology of $(A^\bullet,d_A)$.
--
--   This is the augmentation form of the degenerate-spectral-sequence (staircase) comparison: if each augmented row $0\to A^m\to C^{0,m}\to C^{1,m}\to\cdots$ of a bounded double complex is exact, the total cohomology computes the cohomology of $A^\bullet$. It is the shape in which Čech comparisons are consumed in this development, being cited by the exactness of the columns of the iterated Čech complex for quasi-coherent data and by the identification of the total cohomology of the bi-Čech complex with that of the Čech complex of a product cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DoubleComplex_nonempty_HTot_equiv_of_rows_exact_of_augmentation.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem DoubleComplex.nonempty_HTot_equiv_of_rows_exact_of_augmentation
    {R : Type u} [CommRing R] (D : DoubleComplex.Bounded R)
    (A : ℕ → Type u) [∀ m, AddCommGroup (A m)] [∀ m, Module R (A m)]
    (dA : ∀ m, A m →ₗ[R] A (m + 1)) (ε : ∀ m, A m →ₗ[R] D.C 0 m)
    (hε : ∀ m, Function.Injective (ε m))
    (hεd : ∀ m, D.dV 0 m ∘ₗ ε m = ε (m + 1) ∘ₗ dA m)
    (hker : ∀ m, LinearMap.ker (D.dH 0 m) = LinearMap.range (ε m))
    (hrows : ∀ p m, LinearMap.ker (D.dH (p + 1) m) ≤ LinearMap.range (D.dH p m)) :
    Nonempty (DoubleComplex.HTot D 0 ≃ₗ[R] LinearMap.ker (dA 0)) ∧
      ∀ n : ℕ, Nonempty (DoubleComplex.HTot D (n + 1) ≃ₗ[R]
        (LinearMap.ker (dA (n + 1)) ⧸ (LinearMap.range (dA n)).comap (LinearMap.ker (dA (n + 1))).subtype)) := by sorry
