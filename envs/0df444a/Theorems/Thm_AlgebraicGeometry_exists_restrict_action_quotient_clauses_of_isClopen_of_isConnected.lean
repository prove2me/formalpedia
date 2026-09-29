-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_restrict_action_quotient_clauses_of_isClopen_of_isConnected
-- name    : AlgebraicGeometry.exists_restrict_action_quotient_clauses_of_isClopen_of_isConnected
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/8cffd733-94f7-535d-843e-749ccab6b30d
-- title:
--   Restricting a finite quotient presentation to a clopen connected piece
-- statement:
--   Let $C$ and $X$ be schemes with $X$ having connected underlying space, let $G$ be a finite group and $\rho : G \to \operatorname{Aut} C$ a homomorphism into the automorphism group of $C$ in the category of schemes, and let $\pi : C \to X$ be a finite morphism satisfying: $(\rho g)$ followed by $\pi$ equals $\pi$ for every $g \in G$; $\pi$ is surjective on points; two points of $C$ have the same image under $\pi$ exactly when one is carried to the other by some $(\rho g)$; for every open $V \subseteq X$ the map $\pi^{\ast} : \Gamma(X,V) \to \Gamma(C,\pi^{-1}V)$ is injective; and its image consists precisely of those sections fixed by the action of every $g \in G$ on $\Gamma(C,\pi^{-1}V)$ (via the identification $(\rho g)^{-1}\pi^{-1}V = \pi^{-1}V$ coming from $G$-invariance of $\pi$). Let $U$ be an open subscheme of $C$ whose underlying set is closed and connected (in particular non-empty), and let $G_0 \le G$ be a subgroup whose elements are exactly the $g$ with $(\rho g)^{-1}U = U$. Then there is a homomorphism $\rho_0 : G_0 \to \operatorname{Aut} U$ such that $\rho_0(g)$ followed by the open immersion $U \hookrightarrow C$ equals that immersion followed by $\rho(g)$, and such that the composite $\pi_0 : U \hookrightarrow C \to X$ satisfies, with respect to $\rho_0$, all five of the above clauses: $G_0$-invariance, finiteness, surjectivity on points, fibres equal to $G_0$-orbits, and, on each open $V \subseteq X$, injectivity of $\pi_0^{\ast}$ with image the $G_0$-fixed sections of $\Gamma(U,\pi_0^{-1}V)$.
--
--   This is the statement that a presentation of $X$ as the quotient of $C$ by a finite group $G$ — fibres the orbits, functions the invariants — restricts to a presentation of $X$ as the quotient of a clopen connected piece $U \subseteq C$ by the stabiliser of $U$ in $G$. It is used in the Čerednik–Drinfel'd part of the development, in the construction of a Galois frame for a fine moduli tower where the relevant cardinality identity involves the stabiliser of a component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_restrict_action_quotient_clauses_of_isClopen_of_isConnected.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_restrict_action_quotient_clauses_of_isClopen_of_isConnected
    {C X : Scheme.{0}} [ConnectedSpace X]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut C)
    (π : C ⟶ X) [IsFinite π] (hπ : ∀ g : G, (ρ g).hom ≫ π = π)
    (hsurj : Function.Surjective π.base)
    (horbit : ∀ x x' : C, π.base x = π.base x' ↔ ∃ g : G, (ρ g).hom.base x = x')
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s})
    (U : C.Opens) (hUcl : IsClosed (U : Set C)) (hUconn : _root_.IsConnected (U : Set C))
    (G₀ : Subgroup G) (hG₀ : ∀ g : G, g ∈ G₀ ↔ (ρ g).hom ⁻¹ᵁ U = U) :
    ∃ ρ₀ : G₀ →* Aut (U : Scheme.{0}),
      (∀ g : G₀, (ρ₀ g).hom ≫ U.ι = U.ι ≫ (ρ (g : G)).hom) ∧
      (∃ hπ₀ : ∀ g : G₀, (ρ₀ g).hom ≫ (U.ι ≫ π) = U.ι ≫ π,
        IsFinite (U.ι ≫ π) ∧
        Function.Surjective (U.ι ≫ π).base ∧
        (∀ u u' : (U : Scheme.{0}), (U.ι ≫ π).base u = (U.ι ≫ π).base u' ↔ ∃ g : G₀, (ρ₀ g).hom.base u = u') ∧
        (∀ V : X.Opens, Function.Injective ((U.ι ≫ π).app V)) ∧
        (∀ V : X.Opens, Set.range ((U.ι ≫ π).app V) =
          {s | ∀ g : G₀, (ρ₀ g).hom.appLE ((U.ι ≫ π) ⁻¹ᵁ V) ((U.ι ≫ π) ⁻¹ᵁ V)
            (by rw [← Scheme.Hom.comp_preimage, hπ₀ g]) s = s})) := by sorry
