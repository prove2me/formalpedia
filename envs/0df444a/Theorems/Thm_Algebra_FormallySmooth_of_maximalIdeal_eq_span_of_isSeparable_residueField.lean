-- Prove2me | Theorems.Thm_Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_isSeparable_residueField
-- name    : Algebra.FormallySmooth.of_maximalIdeal_eq_span_of_isSeparable_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/762692e8-1916-5709-b552-d297ed3a948d
-- title:
--   Formal smoothness of a local ring with principal maximal ideal
-- statement:
--   Let $K_0$ be a field and let $\mathcal{O}$ be a commutative ring which is local, a domain and Noetherian, equipped with a $K_0$-algebra structure which is essentially of finite type (that is, $\mathcal{O}$ is a localisation of a finitely generated $K_0$-subalgebra at a submonoid of units, as recorded by `Algebra.EssFiniteType`). Assume given an element $u \in \mathcal{O}$ with $u \neq 0$ such that the maximal ideal of $\mathcal{O}$ is the principal ideal $\mathrm{span}\{u\}$, and assume that the residue field $\mathcal{O}/\mathfrak{m}$ is algebraic over $K_0$ and separable over $K_0$ as a $K_0$-algebra. The conclusion is that the $K_0$-algebra $\mathcal{O}$ is formally smooth, i.e. every $K_0$-algebra map from $\mathcal{O}$ to a quotient $B/I$ by a square-zero ideal lifts to $B$. No regularity or discrete valuation hypothesis is imposed beyond those listed: the principality of the nonzero maximal ideal in a Noetherian local domain is what is used.
--
--   This is the field-coefficient case of the standard criterion that a local ring essentially of finite type over a field, with principal maximal ideal and separable algebraic residue field, is formally smooth (the étale-coordinate argument of EGA IV$_4$ 17.5.3). It is cited by [`Algebra.FormallySmooth.of_maximalIdeal_eq_span_of_perfectField`](thm.html#Algebra.FormallySmooth.of_maximalIdeal_eq_span_of_perfectField), the version over a perfect base field used in the treatment of smoothness of curve charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_isSeparable_residueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open IsLocalRing Polynomial

theorem Algebra.FormallySmooth.of_maximalIdeal_eq_span_of_isSeparable_residueField
    (K₀ : Type u) [Field K₀] (𝒪 : Type v) [CommRing 𝒪] [IsLocalRing 𝒪] [IsDomain 𝒪] [IsNoetherianRing 𝒪]
    [Algebra K₀ 𝒪] [Algebra.EssFiniteType K₀ 𝒪]
    (u : 𝒪) (hu0 : u ≠ 0) (hu : maximalIdeal 𝒪 = Ideal.span {u})
    [Algebra.IsAlgebraic K₀ (ResidueField 𝒪)] [Algebra.IsSeparable K₀ (ResidueField 𝒪)] :
    Algebra.FormallySmooth K₀ 𝒪 := by sorry
