-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_orbit_iff_of_quotient_pullback_of_flat
-- name    : AlgebraicGeometry.Scheme.orbit_iff_of_quotient_pullback_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/ad834f16-dd68-5da1-9124-c2a2709fdc9d
-- title:
--   Orbit fibres persist under flat base change
-- statement:
--   Let $B_0$ and $\mathcal{O}$ be commutative rings and $i : B_0 \to \mathcal{O}$ a ring homomorphism whose associated morphism $\operatorname{Spec}(i)$ of schemes is flat. Let $M, X$ be schemes with structure morphisms $\pi_M : M \to \operatorname{Spec} B_0$ and $\pi_X : X \to \operatorname{Spec} B_0$, and let $\pi : M \to X$ satisfy $\pi$ followed by $\pi_X$ equals $\pi_M$. Let $H$ be a finite group together with a homomorphism $\rho : H \to \operatorname{Aut} M$ such that each $\rho(h)$ commutes with $\pi_M$ and with $\pi$. Assume $\pi$ is integral, affine and surjective on points; that its fibres are exactly the $H$-orbits, i.e. $\pi(x) = \pi(x')$ if and only if $x' = \rho(h)(x)$ for some $h \in H$; that for every open $V \subseteq X$ the ring map $\pi^\sharp$ on $V$ is injective; and that its image consists precisely of those sections of $M$ over $\pi^{-1}V$ fixed by every $\rho(h)$. Let $M', X'$ be schemes over $\operatorname{Spec}\mathcal{O}$ with morphisms $g_M : M' \to M$, $g_X : X' \to X$ exhibiting $M'$ and $X'$ as pullbacks of $M$, respectively $X$, along $\operatorname{Spec}(i)$, let $\pi' : M' \to X'$ be a morphism over $\operatorname{Spec}\mathcal{O}$ compatible with $\pi$ via $g_M, g_X$, and let $\rho' : H \to \operatorname{Aut} M'$ be a homomorphism over $\operatorname{Spec}\mathcal{O}$ with $\rho'(h)$ followed by $g_M$ equal to $g_M$ followed by $\rho(h)$. Then the fibres of $\pi'$ are exactly the $H$-orbits: for all points $y, y'$ of $M'$, $\pi'(y) = \pi'(y')$ if and only if $y' = \rho'(h)(y)$ for some $h \in H$.
--
--   This is the point-set clause of the assertion that a geometric quotient by a finite group is stable under flat base change: the base-changed morphism $\pi'$ again separates exactly the $H$-orbits of the induced action on $M'$. It feeds into the construction of an isomorphism identifying $X'$ with the quotient of $M'$ by $H$, used in [`AlgebraicGeometry.Scheme.exists_iso_quotient_pullback_of_flat`](thm.html#AlgebraicGeometry.Scheme.exists_iso_quotient_pullback_of_flat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_orbit_iff_of_quotient_pullback_of_flat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.orbit_iff_of_quotient_pullback_of_flat
    {B₀ 𝒪 : Type} [CommRing B₀] [CommRing 𝒪] (i : B₀ →+* 𝒪) (hi : Flat (Spec.map (CommRingCat.ofHom i)))
    {M X : Scheme.{0}} (πM : M ⟶ Spec (CommRingCat.of B₀)) (πX : X ⟶ Spec (CommRingCat.of B₀))
    (π : M ⟶ X) (hπX : π ≫ πX = πM)
    {H : Type} [Group H] [Finite H] (ρ : H →* Aut M) (hover : ∀ h : H, (ρ h).hom ≫ πM = πM)
    (hπ : ∀ h : H, (ρ h).hom ≫ π = π)
    (hint : IsIntegralHom π) (haff : IsAffineHom π) (hsurj : Function.Surjective π.base)
    (horbit : ∀ x x' : M, π.base x = π.base x' ↔ ∃ h : H, (ρ h).hom.base x = x')
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ h : H, (ρ h).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s})
    {M' X' : Scheme.{0}} (πM' : M' ⟶ Spec (CommRingCat.of 𝒪)) (πX' : X' ⟶ Spec (CommRingCat.of 𝒪))
    (gM : M' ⟶ M) (hgM : IsPullback gM πM' πM (Spec.map (CommRingCat.ofHom i)))
    (gX : X' ⟶ X) (hgX : IsPullback gX πX' πX (Spec.map (CommRingCat.ofHom i)))
    (π' : M' ⟶ X') (hπX' : π' ≫ πX' = πM') (hπg : π' ≫ gX = gM ≫ π)
    (ρ' : H →* Aut M') (hover' : ∀ h : H, (ρ' h).hom ≫ πM' = πM') (hρg : ∀ h : H, (ρ' h).hom ≫ gM = gM ≫ (ρ h).hom) :
    ∀ y y' : M', π'.base y = π'.base y' ↔ ∃ h : H, (ρ' h).hom.base y = y' := by sorry
