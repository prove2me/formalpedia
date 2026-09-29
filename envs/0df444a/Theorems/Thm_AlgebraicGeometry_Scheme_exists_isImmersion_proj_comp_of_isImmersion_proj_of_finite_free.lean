-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_isImmersion_proj_comp_of_isImmersion_proj_of_finite_free
-- name    : AlgebraicGeometry.Scheme.exists_isImmersion_proj_comp_of_isImmersion_proj_of_finite_free
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/532cabfa-afcf-5e7e-8408-28bd0d469f97
-- title:
--   Immersions into projective space descend along a finite extension
-- statement:
--   Let $S$ and $S'$ be commutative rings with $S'$ an $S$-algebra that is finite and free as an $S$-module, let $X$ be a scheme and let $\pi_X : X \to \operatorname{Spec} S'$ be a morphism of schemes. Assume that $X$ is quasi-projective over $S'$ in the following sense: there exist $a \in \mathbb{N}$ and a morphism $\iota : X \to \operatorname{Proj}$ of the graded ring of homogeneous components of $S'[x_0,\dots,x_a]$, i.e. $\mathbb{P}^a_{S'}$, such that $\iota$ is an immersion and $\iota$ followed by the structure morphism `ProjSpace.π S' a` to $\operatorname{Spec} S'$ equals $\pi_X$. The conclusion asserts the existence of $n \in \mathbb{N}$ and a morphism $\iota' : X \to \mathbb{P}^n_S$ (again $\operatorname{Proj}$ of the homogeneous submodules of $S[x_0,\dots,x_n]$) which is an immersion and satisfies: $\iota'$ followed by `ProjSpace.π S n` equals $\pi_X$ followed by $\operatorname{Spec}$ of the structure map $S \to S'$. No bound on $n$ is recorded.
--
--   This is the permanence of quasi-projectivity under restriction of scalars along a finite ring extension: an immersion into projective space over $S'$ is converted into an immersion into projective space over $S$ compatible with the two structure morphisms. It is used in the construction of quotients of schemes by finite group actions via pullback squares ([`AlgebraicGeometry.Scheme.exists_quotient_isPullback_of_galois_of_finite_action`](thm.html#AlgebraicGeometry.Scheme.exists_quotient_isPullback_of_galois_of_finite_action)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_isImmersion_proj_comp_of_isImmersion_proj_of_finite_free.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.Scheme.exists_isImmersion_proj_comp_of_isImmersion_proj_of_finite_free
    (S : Type) [CommRing S] (S' : Type) [CommRing S'] [Algebra S S'] [Module.Finite S S'] [Module.Free S S']
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of S'))
    (hQP : ∃ (qpa : ℕ) (qpι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpa + 1)) S')),
      IsImmersion qpι ∧ qpι ≫ ProjSpace.π S' qpa = πX) :
    ∃ (qpn : ℕ) (qpι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) S)),
      IsImmersion qpι ∧ qpι ≫ ProjSpace.π S qpn = πX ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')) := by sorry
