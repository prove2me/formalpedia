-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_isAffineOpen_forall_mem_forall_preimage_eq_of_isSeparated_of_finset
-- name    : AlgebraicGeometry.Scheme.exists_isAffineOpen_forall_mem_forall_preimage_eq_of_isSeparated_of_finset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/e2f94930-cc66-561d-936e-014a7add7769
-- title:
--   G-stable affine open containing a finite set of points
-- statement:
--   Let $B$ be a commutative ring and let $X$ be a scheme (in the bottom universe) equipped with a morphism $\pi_X : X \to \operatorname{Spec} B$, where $\operatorname{Spec} B$ is the spectrum of $B$ viewed as a commutative ring object; assume $\pi_X$ is separated. Assume further that $X$ has the property that every finite set $F$ of points of $X$ is contained in some affine open subset of $X$. Let $G$ be a finite group and let $\rho : G \to \operatorname{Aut} X$ be a group homomorphism into the group of automorphisms of $X$ as a scheme (no compatibility of $\rho$ with $\pi_X$ is required). Then for every finite set $F$ of points of $X$ there exists an open subset $U \subseteq X$ such that $U$ is an affine open, every $x \in F$ lies in $U$, and for every $g \in G$ the scheme-theoretic preimage of $U$ along the underlying morphism of the automorphism $\rho(g)$ equals $U$; that is, $U$ is an affine open neighbourhood of $F$ stable under the $G$-action.
--
--   This is the standard step, used when constructing quotients of schemes by finite group actions, that an action of a finite group on a scheme separated over an affine base and having enough affine opens is admissible in the sense that every finite set of points admits a $G$-stable affine open neighbourhood. It is used in the construction of the quotient of $X$ by a finite group action, via [`AlgebraicGeometry.Scheme.exists_quotient_isPullback_of_galois_of_finite_action`](thm.html#AlgebraicGeometry.Scheme.exists_quotient_isPullback_of_galois_of_finite_action).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_isAffineOpen_forall_mem_forall_preimage_eq_of_isSeparated_of_finset.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.Scheme.exists_isAffineOpen_forall_mem_forall_preimage_eq_of_isSeparated_of_finset
    {B : Type} [CommRing B] {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of B)) (hsep : IsSeparated πX)
    (hAF : ∀ F : Finset X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    {G : Type} [Group G] [Finite G] (ρ : G →* Aut X) (F : Finset X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ (∀ x ∈ F, x ∈ U) ∧ ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U := by sorry
