-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_iso_quotient_pullback_of_flat
-- name    : AlgebraicGeometry.Scheme.exists_iso_quotient_pullback_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/6c30cd25-9318-5006-864d-074f5090c9ef
-- title:
--   Finite-group quotients commute with flat base change
-- statement:
--   Let $i : B_0 \to \mathcal{O}$ be a ring homomorphism whose associated morphism $\operatorname{Spec}(i)$ is flat. Over $\operatorname{Spec} B_0$ one is given schemes $\pi_M : M \to \operatorname{Spec} B_0$, $\pi_X : X \to \operatorname{Spec} B_0$ and a morphism $\pi : M \to X$ with $\pi$ followed by $\pi_X$ equal to $\pi_M$, together with an action $\rho$ of a finite group $H$ by automorphisms of $M$ fixing $\pi_M$ and $\pi$, such that $\pi$ is integral, affine and surjective on points, two points of $M$ have the same image under $\pi$ exactly when they lie in one $H$-orbit, each $\pi^\sharp$ on sections over an open $V \subseteq X$ is injective with image exactly the sections of $M$ over $\pi^{-1}V$ invariant under all $\rho(h)$, and $\pi$ is a categorical quotient: every $H$-invariant $f : M \to T$ factors uniquely through $\pi$. Let $g_M : M' \to M$, $\pi_{M'} : M' \to \operatorname{Spec} \mathcal{O}$ exhibit $M'$ as the pullback of $\pi_M$ along $\operatorname{Spec}(i)$, with an action $\rho'$ of $H$ on $M'$ over $\mathcal{O}$ compatible with $\rho$ via $g_M$. Let $\pi_Y : M' \to Y$ over $\pi_{Y,b} : Y \to \operatorname{Spec}\mathcal{O}$ satisfy the same list of conditions for $(M', \rho')$. Then there is a morphism $e : Y \to X \times_{\operatorname{Spec} B_0} \operatorname{Spec}\mathcal{O}$ which is an isomorphism, which is compatible with the structure morphisms to $\operatorname{Spec}\mathcal{O}$, and for which $\pi_Y$ followed by $e$ is the morphism $M' \to X \times_{\operatorname{Spec} B_0} \operatorname{Spec}\mathcal{O}$ induced by $g_M$ followed by $\pi$ and by $\pi_{M'}$.
--
--   This is the statement that the formation of a quotient of a scheme by a finite group, in the explicit integral-affine-invariants sense used here, commutes with flat base change on the base ring: any quotient of the base-changed scheme is canonically isomorphic to the base change of the quotient. It is used in the Čerednik–Drinfeld part of the development, to compare fine moduli schemes of quaternionic data over $B_0$ with their base changes to $\mathcal{O}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_iso_quotient_pullback_of_flat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_iso_quotient_pullback_of_flat
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
    (hcat : ∀ (T : Scheme.{0}) (f : M ⟶ T), (∀ h : H, (ρ h).hom ≫ f = f) → ∃! f' : X ⟶ T, π ≫ f' = f)

    {M' : Scheme.{0}} (πM' : M' ⟶ Spec (CommRingCat.of 𝒪))
    (gM : M' ⟶ M) (hgM : IsPullback gM πM' πM (Spec.map (CommRingCat.ofHom i)))
    (ρ' : H →* Aut M') (hover' : ∀ h : H, (ρ' h).hom ≫ πM' = πM') (hρg : ∀ h : H, (ρ' h).hom ≫ gM = gM ≫ (ρ h).hom)

    {Y : Scheme.{0}} (πYb : Y ⟶ Spec (CommRingCat.of 𝒪)) (πY : M' ⟶ Y) (hπYb : πY ≫ πYb = πM')
    (hπY : ∀ h : H, (ρ' h).hom ≫ πY = πY)
    (hintY : IsIntegralHom πY) (haffY : IsAffineHom πY) (hsurjY : Function.Surjective πY.base)
    (horbitY : ∀ y y' : M', πY.base y = πY.base y' ↔ ∃ h : H, (ρ' h).hom.base y = y')
    (hsecY : ∀ V : Y.Opens, Function.Injective (πY.app V))
    (hinvY : ∀ V : Y.Opens, Set.range (πY.app V) =
      {s | ∀ h : H, (ρ' h).hom.appLE (πY ⁻¹ᵁ V) (πY ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπY h]) s = s})
    (hcatY : ∀ (T : Scheme.{0}) (f : M' ⟶ T), (∀ h : H, (ρ' h).hom ≫ f = f) → ∃! f' : Y ⟶ T, πY ≫ f' = f) :
    ∃ e : Y ⟶ pullback πX (Spec.map (CommRingCat.ofHom i)),
      IsIso e ∧ e ≫ pullback.snd πX (Spec.map (CommRingCat.ofHom i)) = πYb ∧
      πY ≫ e = pullback.lift (gM ≫ π) πM' (by rw [Category.assoc, hπX, hgM.w]) := by sorry
