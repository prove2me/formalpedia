-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_restrict_action_quotient_clauses_morphismRestrict
-- name    : AlgebraicGeometry.exists_restrict_action_quotient_clauses_morphismRestrict
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/3b66c4dd-6a48-5d94-8bb7-2337039b5c67
-- title:
--   Finite-group quotient clauses restrict to an open of the target
-- statement:
--   Let $M$ and $X$ be schemes, $G$ a finite group, $\rho : G \to \operatorname{Aut} M$ a group homomorphism into the automorphisms of $M$ as a scheme, and $\pi : M \to X$ a finite morphism. Assume: $\pi$ is $G$-invariant, i.e. $\rho(g)$ followed by $\pi$ equals $\pi$ for every $g$; the underlying continuous map of $\pi$ is surjective; for all points $x, x'$ of $M$ one has $\pi(x) = \pi(x')$ if and only if $x' = \rho(g)(x)$ for some $g \in G$; for every open $V \subseteq X$ the map on sections $\Gamma(X,V) \to \Gamma(M, \pi^{-1}V)$ is injective; and for every such $V$ its image is exactly the set of $s \in \Gamma(M,\pi^{-1}V)$ fixed by all the maps induced by $\rho(g)$ on $\Gamma(M,\pi^{-1}V)$ (using $\rho(g)^{-1}(\pi^{-1}V) = \pi^{-1}V$, which follows from invariance). Let $U \subseteq X$ be open. Then there is a group homomorphism $\rho' : G \to \operatorname{Aut}(\pi^{-1}U)$, viewing the open subscheme $\pi^{-1}U$ of $M$ as a scheme, such that $\rho'(g)$ followed by the inclusion $\pi^{-1}U \hookrightarrow M$ equals that inclusion followed by $\rho(g)$, and such that, for a chosen witness of the invariance $\rho'(g)$ followed by $\pi|_U$ equals $\pi|_U$, the restricted morphism $\pi|_U : \pi^{-1}U \to U$ satisfies the same five clauses: it is finite, surjective on points, its fibres are exactly the $\rho'$-orbits, and for every open $V \subseteq U$ the map $\Gamma(U,V) \to \Gamma(\pi^{-1}U, (\pi|_U)^{-1}V)$ is injective with image the sections fixed by all $\rho'(g)$. The invariance witness is existentially bound because the last clause's statement depends on it.
--
--   This is the localisation of the target in the statement that a finite surjective morphism with orbit fibres and invariant-section image presents $X$ as the quotient $M/G$: all five clauses descend to $\pi^{-1}U \to U$ for an arbitrary open $U \subseteq X$. It is used in the Čerednik–Drinfel'd part of the development, where a Galois frame on a moduli tower is produced over an open piece of the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_restrict_action_quotient_clauses_morphismRestrict.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_restrict_action_quotient_clauses_morphismRestrict
    {M X : Scheme.{u}} (G : Type u) [Group G] [Finite G] (ρ : G →* Aut M)
    (π : M ⟶ X) [IsFinite π] (hπ : ∀ g : G, (ρ g).hom ≫ π = π)
    (hsurj : Function.Surjective π.base)
    (horbit : ∀ x x' : M, π.base x = π.base x' ↔ ∃ g : G, (ρ g).hom.base x = x')
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s})
    (U : X.Opens) :
    ∃ ρ' : G →* Aut ((π ⁻¹ᵁ U : M.Opens) : Scheme.{u}),
      (∀ g : G, (ρ' g).hom ≫ (π ⁻¹ᵁ U).ι = (π ⁻¹ᵁ U).ι ≫ (ρ g).hom) ∧
      (∃ hπ' : ∀ g : G, (ρ' g).hom ≫ (π ∣_ U) = π ∣_ U,
        IsFinite (π ∣_ U) ∧
        Function.Surjective (π ∣_ U).base ∧
        (∀ u u' : ((π ⁻¹ᵁ U : M.Opens) : Scheme.{u}), (π ∣_ U).base u = (π ∣_ U).base u' ↔ ∃ g : G, (ρ' g).hom.base u = u') ∧
        (∀ V : (U : Scheme.{u}).Opens, Function.Injective ((π ∣_ U).app V)) ∧
        (∀ V : (U : Scheme.{u}).Opens, Set.range ((π ∣_ U).app V) =
          {s | ∀ g : G, (ρ' g).hom.appLE ((π ∣_ U) ⁻¹ᵁ V) ((π ∣_ U) ⁻¹ᵁ V)
            (by rw [← Scheme.Hom.comp_preimage, hπ' g]) s = s})) := by sorry
