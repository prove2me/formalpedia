-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_opens_isClosed_preimage_eq_existsUnique_of_quotient
-- name    : AlgebraicGeometry.Scheme.exists_opens_isClosed_preimage_eq_existsUnique_of_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/1677866b-eb77-54e4-802f-f620023f6aa5
-- title:
--   Categorical quotients by finite groups restrict to clopen stable pieces
-- statement:
--   Let $M$ and $X$ be schemes, $H$ a finite group, and $\rho : H \to \operatorname{Aut} M$ a group homomorphism. Let $\pi : M \to X$ be a morphism satisfying: $\pi$ is invariant, i.e. the underlying morphism of $\rho(h)$ followed by $\pi$ equals $\pi$ for every $h \in H$; $\pi$ is an integral morphism; the map of underlying spaces $\pi$ is surjective; the fibres of $\pi$ on points are exactly the $H$-orbits, i.e. $\pi(x) = \pi(x')$ if and only if $x' = \rho(h)(x)$ for some $h \in H$; and $\pi$ is a categorical quotient, i.e. for every scheme $T$ and every $f : M \to T$ with $\rho(h)$ followed by $f$ equal to $f$ for all $h$, there is a unique $f' : X \to T$ with $\pi$ followed by $f'$ equal to $f$. Let $V$ be an open subscheme of $M$ whose underlying set is closed and which is $H$-stable in the sense that the scheme-theoretic preimage of $V$ under each $\rho(h)$ is $V$. Then there is an open subscheme $U$ of $X$ with $\pi^{-1}(U) = V$ such that the underlying set of $U$ is closed in $X$, equals the image of $V$ under $\pi$, and the restriction $V \to U$ of $\pi$ is again a categorical quotient: for every scheme $T$ and every $f : V \to T$ invariant under the restrictions of the $\rho(h)$ to $V$, there is a unique $f' : U \to T$ whose composition after the restricted morphism $V \to U$ is $f$.
--
--   This is the statement that a categorical quotient of a scheme by a finite group, when it is integral, surjective and has the orbits as its fibres, restricts to a categorical quotient over any open-and-closed $H$-stable piece of the source. It is used in the construction of coarse moduli schemes for quaternionic data, where a fine moduli scheme with a finite group action is cut into stable clopen pieces before passing to the quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_opens_isClosed_preimage_eq_existsUnique_of_quotient.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_opens_isClosed_preimage_eq_existsUnique_of_quotient
    {M X : Scheme.{u}} {H : Type} [Group H] [Finite H] (ρ : H →* Aut M) (π : M ⟶ X)
    (hπ : ∀ h : H, (ρ h).hom ≫ π = π) (hint : IsIntegralHom π) (hsurj : Function.Surjective π.base)
    (horbit : ∀ x x' : M, π.base x = π.base x' ↔ ∃ h : H, (ρ h).hom.base x = x')
    (hcat : ∀ (T : Scheme.{u}) (f : M ⟶ T), (∀ h : H, (ρ h).hom ≫ f = f) → ∃! f' : X ⟶ T, π ≫ f' = f)
    (V : M.Opens) (hVcl : IsClosed (V : Set M)) (hV : ∀ h : H, (ρ h).hom ⁻¹ᵁ V = V) :
    ∃ (U : X.Opens) (hUV : π ⁻¹ᵁ U = V), IsClosed (U : Set X) ∧ Set.image π.base (V : Set M) = (U : Set X) ∧
      ∀ (T : Scheme.{u}) (f : (V : Scheme.{u}) ⟶ T),
        (∀ h : H, (ρ h).hom.resLE V V (by rw [hV h]) ≫ f = f) →
        ∃! f' : (U : Scheme.{u}) ⟶ T, π.resLE U V (by rw [hUV]) ≫ f' = f := by sorry
