-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isGalois_functionField_of_quotient_of_finite
-- name    : AlgebraicGeometry.exists_isGalois_functionField_of_quotient_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/a0b1b3cb-e02a-518c-891a-4fb1ca51a18f
-- title:
--   Function field of a finite-group quotient is Galois
-- statement:
--   Let $B$ be a commutative ring, and let $C$ and $X$ be integral schemes (in the base universe). Assume given a separated morphism $\pi_C : C \to \operatorname{Spec} B$, a finite group $G$, and a group homomorphism $\rho : G \to \operatorname{Aut} C$ such that for each $g$ the underlying morphism of $\rho g$ followed by $\pi_C$ is $\pi_C$, so that $G$ acts over the affine base. Assume further given a finite morphism $\pi : C \to X$ with $\rho g$ followed by $\pi$ equal to $\pi$ for all $g$, such that: the map of topological spaces underlying $\pi$ is surjective; for every open $V \subseteq X$ the ring map $\Gamma(X,V) \to \Gamma(C, \pi^{-1}V)$ is injective; and its image consists exactly of those sections $s$ with $(\rho g)$ acting on $\Gamma(C,\pi^{-1}V)$ (via the restriction of $(\rho g)$ to the $G$-stable open $\pi^{-1}V$) fixing $s$, for all $g \in G$. The conclusion asserts the existence of an $X.\mathrm{functionField}$-algebra structure on $C.\mathrm{functionField}$ together with a group homomorphism $\theta$ from $G$ to the group of $X.\mathrm{functionField}$-algebra automorphisms of $C.\mathrm{functionField}$, subject to: the structure map sends the germ at the generic point of $f \in \Gamma(X,V)$ to the germ of $\pi^\ast f \in \Gamma(C,\pi^{-1}V)$, for every open $V$ with $V$ and $\pi^{-1}V$ non-empty; $\theta g$ sends the germ of $f \in \Gamma(C,U)$ to the germ of the pull-back of $f$ along the inverse of $\rho g$, for every open $U$ with $U$ and the preimage of $U$ under that inverse non-empty; the extension $C.\mathrm{functionField}/X.\mathrm{functionField}$ is finite-dimensional and Galois; $\theta$ is surjective; and $\theta g = 1$ precisely when $\rho g = 1$.
--
--   This is the function-field form of the Galois theory of a quotient of an integral scheme by a finite group: the quotient hypotheses (surjectivity, and sections over $X$ being exactly the $G$-invariant sections over $C$) force $K(C)/K(X)$ to be finite Galois with group $G$ modulo the subgroup acting trivially on $C$. It is used in the Čerednik–Drinfel'd part of the development, to produce a Galois frame for a quotient of a fine moduli tower together with a count relating stabiliser orders to the degree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isGalois_functionField_of_quotient_of_finite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_isGalois_functionField_of_quotient_of_finite
    {B : Type} [CommRing B]
    {C X : Scheme.{0}} [IsIntegral C] [IsIntegral X]
    (πC : C ⟶ Spec (CommRingCat.of B)) [IsSeparated πC]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut C) (hρ : ∀ g : G, (ρ g).hom ≫ πC = πC)
    (π : C ⟶ X) [IsFinite π] (hπ : ∀ g : G, (ρ g).hom ≫ π = π)
    (hsurj : Function.Surjective π.base)
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s}) :
    ∃ (_ : Algebra X.functionField C.functionField)
      (θ : G →* (C.functionField ≃ₐ[X.functionField] C.functionField)),

      (∀ (V : X.Opens) [Nonempty (V : Scheme.{0})] [Nonempty ((π ⁻¹ᵁ V : C.Opens) : Scheme.{0})] (f : Γ(X, V)),
        algebraMap X.functionField C.functionField (X.germToFunctionField V f) =
          C.germToFunctionField (π ⁻¹ᵁ V) (π.app V f)) ∧

      (∀ (g : G) (U : C.Opens) [Nonempty (U : Scheme.{0})] [Nonempty (((ρ g).inv ⁻¹ᵁ U : C.Opens) : Scheme.{0})] (f : Γ(C, U)),
        θ g (C.germToFunctionField U f) = C.germToFunctionField ((ρ g).inv ⁻¹ᵁ U) ((ρ g).inv.app U f)) ∧
      FiniteDimensional X.functionField C.functionField ∧ IsGalois X.functionField C.functionField ∧
      Function.Surjective θ ∧ (∀ g : G, θ g = 1 ↔ ρ g = 1) := by sorry
