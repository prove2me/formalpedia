-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor
-- name    : AlgebraicCurve.exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/84edbd51-87ee-5416-b884-5165e51ad295
-- title:
--   Flag-adapted basis of L(MD) up to level M₁
-- statement:
--   Let $F$ be a field extension of a field $K$, and let $x \in F$ be transcendental over $K$. Here a place $v$ of $F/K$ is a valuation subring of $F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring; a divisor is a finitely supported function from places to $\mathbb{Z}$; and for a divisor $D$ the space $\mathcal{L}(D) =$ `LSpace D` is the $K$-subspace of those $f \in F$ with $v(f) \le \exp(D v)$ at every place $v$, where $v$ denotes the associated adic valuation, and $\ell(D)$ its $K$-dimension. Assume $D$ is the pole divisor of $x$, i.e. $D v = \max(0, -\operatorname{ord}_v x)$ at every place $v$, where $\operatorname{ord}_v x = -\log v(x)$; assume each $\mathcal{L}(M \cdot D)$ is finite-dimensional over $K$ for $M \in \mathbb{N}$; and assume $\ell(0) = 1$. Then for every $M_1 \in \mathbb{N}$ there are $d' \in \mathbb{N}$, elements $y_\sigma \in F$ and exponents $e_\sigma \in \mathbb{N}$ indexed by $\sigma \in \mathrm{Fin}\, d'$, such that $e_\sigma \le M_1$ and $y_\sigma \in \mathcal{L}(e_\sigma \cdot D)$ for all $\sigma$, and such that for every $M \le M_1$: first, $\mathcal{L}(M \cdot D)$ is contained in the $K$-span of $\{x^j y_\sigma : j + e_\sigma \le M\}$; and second, the family $(\sigma, j) \mapsto x^j y_\sigma$, indexed by the pairs with $j + e_\sigma \le M$, is $K$-linearly independent. Only the one inclusion of spaces is asserted, not equality.
--
--   This is the finite-stage construction, for all levels $M \le M_1$ simultaneously, of a basis of the filtration $\mathcal{L}(M \cdot D)$ by the pole divisor $D$ of a transcendental element $x$, adapted to the flag in the sense of the reduced bases of Deuring and Roquette: each basis element has the shape $x^j y_\sigma$ with the level of $y_\sigma$ recorded by $e_\sigma$. It feeds the unbounded version [`AlgebraicCurve.exists_flagAdaptedBasis_lSpace_nsmul_poleDivisor`](thm.html#AlgebraicCurve.exists_flagAdaptedBasis_lSpace_nsmul_poleDivisor), used in the dimension estimates for the adelic index of divisors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_flagAdaptedBasisAt_lSpace_nsmul_poleDivisor
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (hFD : ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)))
    (hell0 : ell (0 : Divisor K F) = 1) (M₁ : ℕ) :
    ∃ (d' : ℕ) (y : Fin d' → F) (e : Fin d' → ℕ),
      (∀ σ, e σ ≤ M₁) ∧
      (∀ σ, y σ ∈ LSpace ((e σ) • D)) ∧
      (∀ M ≤ M₁, (LSpace (M • D) : Submodule K F)
        ≤ Submodule.span K {z | ∃ σ j, j + e σ ≤ M ∧ z = x ^ j * y σ}) ∧
      (∀ M ≤ M₁, LinearIndependent K
        (fun p : {p : Fin d' × ℕ // p.2 + e p.1 ≤ M} => x ^ p.val.2 * y p.val.1)) := by sorry
