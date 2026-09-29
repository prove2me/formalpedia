-- Prove2me | Theorems.Thm_AlgebraicGeometry_DescentCharacter_isBaseScalar_pullback_map
-- name    : AlgebraicGeometry.DescentCharacter.isBaseScalar_pullback_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/1c08ba73-27d4-52ff-9736-30de16cadd97
-- title:
--   Base-scalar endomorphisms pull back along φ
-- statement:
--   Let $g\colon X'\to X$ be a morphism of schemes, let $R$ and $R'$ be commutative rings, let $f\colon X\to\operatorname{Spec} R$ and $f'\colon X'\to\operatorname{Spec} R'$ be morphisms of schemes, let $\varphi\colon R\to R'$ be a ring homomorphism, and assume the square commutes in the sense that $g$ followed by $f$ equals $f'$ followed by $\operatorname{Spec}\varphi$. Let $M$ be an $\mathcal O_X$-module and $\sigma\colon M\to M$ an endomorphism of it, and let $c\in R$. The hypothesis is `IsBaseScalar f σ c`: for every open $U\subseteq X$ and every $s\in\Gamma(M,U)$ one has $\sigma_U(s)=\mathrm{baseSection}\,f\,c\,U\cdot s$, where $\mathrm{baseSection}\,f\,c\,U\in\Gamma(X,U)$ is the restriction to $U$ of the global function obtained by applying $f$ on global sections to the element of $\Gamma(\operatorname{Spec} R,\top)$ corresponding to $c$ under the inverse of the canonical isomorphism $\Gamma(\operatorname{Spec} R)\cong R$. The conclusion is `IsBaseScalar f' ((Scheme.Modules.pullback g).map σ) (φ c)`: the image of $\sigma$ under the pull-back functor on modules along $g$ satisfies the same property over $f'$ with constant $\varphi(c)$, i.e. on every open $V\subseteq X'$ it acts on $\Gamma((\mathrm{pullback}\ g)(M),V)$ as multiplication by the restriction to $V$ of the global function on $X'$ attached to $\varphi(c)$ via $f'$.
--
--   This is the compatibility of "multiplication by a constant of the base ring" with inverse images of sheaves of modules: an endomorphism which is multiplication by $c\in R$ pulls back, along a morphism lying over $\varphi\colon R\to R'$, to multiplication by $\varphi(c)$. It feeds the descent-character bookkeeping, being used by the statements on composing and base-changing the "has value" predicate and on the normalisation of base-scalar endomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_DescentCharacter_isBaseScalar_pullback_map.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.DescentCharacter

universe u

theorem AlgebraicGeometry.DescentCharacter.isBaseScalar_pullback_map
    {X X' : Scheme.{u}} (g : X' ⟶ X) {R R' : Type u} [CommRing R] [CommRing R']
    (f : X ⟶ Spec (CommRingCat.of R)) (f' : X' ⟶ Spec (CommRingCat.of R')) (φ : R →+* R')
    (hg : g ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ))
    {M : X.Modules} {σ : M ⟶ M} {c : R} (hσ : IsBaseScalar f σ c) :
    IsBaseScalar f' ((Scheme.Modules.pullback g).map σ) (φ c) := by sorry
