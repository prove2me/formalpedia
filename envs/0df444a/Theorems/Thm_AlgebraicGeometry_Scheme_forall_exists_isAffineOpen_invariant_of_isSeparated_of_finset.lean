-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_forall_exists_isAffineOpen_invariant_of_isSeparated_of_finset
-- name    : AlgebraicGeometry.Scheme.forall_exists_isAffineOpen_invariant_of_isSeparated_of_finset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/c0d1a001-0366-58a6-bf35-69731afa2470
-- title:
--   Invariant affine neighbourhoods for a finite group action
-- statement:
--   Let $B$ be a commutative ring and $X$ a scheme, and let $\pi_X : X \to \operatorname{Spec} B$ be a morphism of schemes which is separated. Assume further that every finite subset $F$ of the underlying space of $X$ is contained in some affine open subset of $X$, i.e. for each finite $F$ there is an open $U \subseteq X$ with $U$ affine and $F \subseteq U$. Let $G$ be a finite group acting on $X$ by a group homomorphism $\rho : G \to \operatorname{Aut} X$ into the automorphism group of $X$ in the category of schemes. Then every point $x$ of $X$ admits an open subset $U \subseteq X$ such that $U$ is affine, $x \in U$, and $U$ is invariant in the strong sense that for every $g \in G$ the scheme-theoretic preimage of $U$ along the underlying morphism of $\rho(g)$ is equal to $U$ (not merely contained in it). No compatibility between the action $\rho$ and the structure morphism $\pi_X$ is assumed; $\pi_X$ enters only through the separatedness hypothesis.
--
--   This is the standard construction of $G$-stable affine open neighbourhoods for a finite group acting on a separated scheme whose finite subsets lie in affine opens, the hypothesis needed to form quotients of schemes by finite group actions. It feeds [`AlgebraicGeometry.Scheme.exists_quotient_isPullback_of_galois_of_finite_action`](thm.html#AlgebraicGeometry.Scheme.exists_quotient_isPullback_of_galois_of_finite_action) and, through it, the construction and integrality statements for the coarse moduli schemes used in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_forall_exists_isAffineOpen_invariant_of_isSeparated_of_finset.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

universe u v

theorem AlgebraicGeometry.Scheme.forall_exists_isAffineOpen_invariant_of_isSeparated_of_finset
    {B : Type u} [CommRing B] {X : Scheme.{u}} (πX : X ⟶ Spec (CommRingCat.of B)) (hsep : IsSeparated πX)
    (hAF : ∀ F : Finset X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    {G : Type v} [Group G] [Finite G] (ρ : G →* Aut X) :
    ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U := by sorry
