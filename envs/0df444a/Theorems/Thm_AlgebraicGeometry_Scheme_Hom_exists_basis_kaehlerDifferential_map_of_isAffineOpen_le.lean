-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehlerDifferential_map_of_isAffineOpen_le
-- name    : AlgebraicGeometry.Scheme.Hom.exists_basis_kaehlerDifferential_map_of_isAffineOpen_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/cb9fdf50-d9a8-5ddf-97bf-30749567bc1a
-- title:
--   Restricting a basis of Kähler differentials to a smaller affine open
-- statement:
--   Let $B$ be a commutative ring, $X$ a scheme and $gX : X \to \operatorname{Spec} B$ a morphism of schemes. Let $W$ and $W'$ be opens of $X$, both assumed affine (hypotheses `hW`, `hW'`), with $W' \le W$, and let $\iota$ be an index type (in an arbitrary universe). The sections over an open $U$ are given the $B$-algebra structure `sectionsAlgebra`, namely the ring map obtained from the inverse of $\Gamma(\operatorname{Spec} B) \cong B$ followed by $gX^{\sharp}$ from the top open to $U$; thus $\Gamma(X,W)$ and $\Gamma(X,W')$ are $B$-algebras. Moreover $\Gamma(X,W')$ is made a $\Gamma(X,W)$-algebra by the restriction map $X.\mathrm{presheaf}$ applied to the inclusion $W' \le W$. Assuming these three structures form a scalar tower, the assertion is: for every basis $b$ of the module of Kähler differentials $\Omega_{\Gamma(X,W)/B}$ over $\Gamma(X,W)$, indexed by $\iota$, there exists a basis $b'$ of $\Omega_{\Gamma(X,W')/B}$ over $\Gamma(X,W')$, indexed by the same $\iota$, such that for every $i$ one has $b'(i) = \mathrm{KaehlerDifferential.map}\,(b(i))$, the image of $b(i)$ under the canonical map $\Omega_{\Gamma(X,W)/B} \to \Omega_{\Gamma(X,W')/B}$ induced by the identity on $B$ and the restriction map.
--
--   This is the statement that a basis of relative differentials on an affine chart restricts to a basis on any smaller affine chart, the algebraic form of the fact that an inclusion of affine opens is étale and hence induces a base-change isomorphism on differentials. It is used in the construction of local frames for differentials on smooth schemes, and is cited in the proof that a morphism built from a pullback of smooth relative dimension data is an isomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehlerDifferential_map_of_isAffineOpen_le.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_KaehlerModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

theorem AlgebraicGeometry.Scheme.Hom.exists_basis_kaehlerDifferential_map_of_isAffineOpen_le
    {B : Type u} [CommRing B] {X : Scheme.{u}} (gX : X ⟶ Spec (CommRingCat.of B))
    {W W' : X.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hle : W' ≤ W) {ι : Type v} :
    letI := gX.sectionsAlgebra W; letI := gX.sectionsAlgebra W'
    letI : Algebra Γ(X, W) Γ(X, W') := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    ∀ [IsScalarTower B Γ(X, W) Γ(X, W')] (b : Module.Basis ι Γ(X, W) (Ω[Γ(X, W)⁄B])),
      ∃ b' : Module.Basis ι Γ(X, W') (Ω[Γ(X, W')⁄B]),
        ∀ i, b' i = KaehlerDifferential.map B B Γ(X, W) Γ(X, W') (b i) := by sorry
