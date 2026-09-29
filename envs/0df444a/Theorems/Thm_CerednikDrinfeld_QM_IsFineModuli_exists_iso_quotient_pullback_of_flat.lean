-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_iso_quotient_pullback_of_flat
-- name    : CerednikDrinfeld.QM.IsFineModuli.exists_iso_quotient_pullback_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/c20ef931-fdc7-5e2d-acd7-58c3de2d6b19
-- title:
--   Quotients of the fine moduli scheme commute with flat base change
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathbb{Z}$ the algebra stays a division algebra after tensoring with the completion at $v$ exactly when $v$ lies above $q$ or $q'$; let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be an order maximal among orders, let $N \geq 1$ and $m \geq 3$, and let $i : B_0 \to \mathcal{O}$ be a ring map whose associated morphism of affine schemes is flat, with $N$ and $m$ invertible in $B_0$. Assume given a scheme $M_0$ over $\operatorname{Spec} B_0$ together with $\mathrm{ptF}_0$, and a scheme $M$ over $\operatorname{Spec}\mathcal{O}$ together with $\mathrm{ptF}$, each satisfying `IsFineModuli` for $\Lambda$, $N$, $m$: the assignment sending an $S$-point $s$ of the base and a pair consisting of a fake elliptic curve with $\Lambda$-action and level-$N$ structure over $S$ together with a full level-$m$ structure to a morphism over $s$ is invariant under isomorphisms of such data, compatible with base change of the ring, surjective onto all morphisms over $s$, and injective up to isomorphism. Assume further finite groups $G_0$, $G$ acting by automorphisms $\rho_0$, $\rho$ with labels $\chi_0$, $\chi$ valued in $\Lambda$ satisfying `IsLevelTwistAction`: the automorphisms commute with the structure morphism, applying $\rho$ to a moduli point realises the twist by the label, and the labels are multiplicative, surjective and injective modulo $m\Lambda$. Let $H$ be a finite group with injective homomorphisms $\varphi_0 : H \to G_0$ and $\varphi : H \to G$ whose labels agree modulo $m\Lambda$, i.e. $\chi_0(\varphi_0 h) - \chi(\varphi h) \in m\Lambda$ for all $h$. Finally let $\pi_0 : M_0 \to X_0$ over $\operatorname{Spec} B_0$ and $\pi : M \to X$ over $\operatorname{Spec}\mathcal{O}$ each exhibit the target as the quotient by the image of $H$, in the sense that $\pi$ is compatible with the structure morphisms and invariant under the action, is integral, affine and surjective on points, its fibres are exactly the $H$-orbits, the maps on sections are injective with image the $H$-invariant sections, and $\pi$ has the universal property among $H$-invariant morphisms out of $M$ (likewise for $\pi_0$). Then there is a morphism $e : X \to X_0 \times_{\operatorname{Spec} B_0} \operatorname{Spec}\mathcal{O}$ which is an isomorphism and satisfies $e$ followed by the second projection $= \pi_X$, i.e. an isomorphism over $\operatorname{Spec}\mathcal{O}$.
--
--   This is the flat base-change compatibility of the quotient of the fine moduli scheme of fake elliptic curves with full level-$m$ structure by a finite group of level twists: the coarse quotient over $\mathcal{O}$ is the base change of the one over $B_0$. It is used to transport properties of the quotient proved over a convenient base $B_0$ (flatness and local finite type, and smoothness of relative dimension one) to the quotient over $\mathcal{O}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_exists_iso_quotient_pullback_of_flat.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsFineModuli.exists_iso_quotient_pullback_of_flat
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q) {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N m : ℕ) [NeZero N] (hm : 3 ≤ m)
    {B₀ 𝒪 : Type} [CommRing B₀] [CommRing 𝒪] (i : B₀ →+* 𝒪) (hi : Flat (Spec.map (CommRingCat.ofHom i)))
    (hN : IsUnit ((N : ℕ) : B₀)) (hm' : IsUnit ((m : ℕ) : B₀))

    {M₀ : Scheme.{0}} {πM₀ : M₀ ⟶ Spec (CommRingCat.of B₀)}
    {ptF₀ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B₀)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM₀}
    (hM₀ : IsFineModuli Λ N m M₀ πM₀ ptF₀)
    {G₀ : Type} [Group G₀] [Finite G₀] {ρ₀ : G₀ →* Aut M₀} {χ₀ : G₀ → ↥Λ} (hρ₀ : IsLevelTwistAction Λ N m M₀ πM₀ ptF₀ G₀ ρ₀ χ₀)
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF)
    {G : Type} [Group G] [Finite G] {ρ : G →* Aut M} {χ : G → ↥Λ} (hρ : IsLevelTwistAction Λ N m M πM ptF G ρ χ)

    (H : Type) [Group H] [Finite H] (φ₀ : H →* G₀) (hφ₀ : Function.Injective φ₀) (φ : H →* G) (hφ : Function.Injective φ)
    (hlabel : ∀ h : H, ∃ y : ↥Λ, (χ₀ (φ₀ h) : ℍ[ℚ, a, b]) - (χ (φ h) : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]))

    (X₀ : Scheme.{0}) (πX₀ : X₀ ⟶ Spec (CommRingCat.of B₀)) (π₀ : M₀ ⟶ X₀) (hπX₀ : π₀ ≫ πX₀ = πM₀)
    (hπ₀ : ∀ h : H, (ρ₀ (φ₀ h)).hom ≫ π₀ = π₀)
    (hint₀ : IsIntegralHom π₀) (haff₀ : IsAffineHom π₀) (hsurj₀ : Function.Surjective π₀.base)
    (horbit₀ : ∀ x x' : M₀, π₀.base x = π₀.base x' ↔ ∃ h : H, (ρ₀ (φ₀ h)).hom.base x = x')
    (hsec₀ : ∀ V : X₀.Opens, Function.Injective (π₀.app V))
    (hinv₀ : ∀ V : X₀.Opens, Set.range (π₀.app V) =
      {s | ∀ h : H, (ρ₀ (φ₀ h)).hom.appLE (π₀ ⁻¹ᵁ V) (π₀ ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ₀ h]) s = s})
    (hcat₀ : ∀ (T : Scheme.{0}) (f : M₀ ⟶ T), (∀ h : H, (ρ₀ (φ₀ h)).hom ≫ f = f) → ∃! f' : X₀ ⟶ T, π₀ ≫ f' = f)
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of 𝒪)) (π : M ⟶ X) (hπX : π ≫ πX = πM)
    (hπ : ∀ h : H, (ρ (φ h)).hom ≫ π = π)
    (hint : IsIntegralHom π) (haff : IsAffineHom π) (hsurj : Function.Surjective π.base)
    (horbit : ∀ x x' : M, π.base x = π.base x' ↔ ∃ h : H, (ρ (φ h)).hom.base x = x')
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ h : H, (ρ (φ h)).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s})
    (hcat : ∀ (T : Scheme.{0}) (f : M ⟶ T), (∀ h : H, (ρ (φ h)).hom ≫ f = f) → ∃! f' : X ⟶ T, π ≫ f' = f) :
    ∃ e : X ⟶ Limits.pullback πX₀ (Spec.map (CommRingCat.ofHom i)),
      IsIso e ∧ e ≫ Limits.pullback.snd πX₀ (Spec.map (CommRingCat.ofHom i)) = πX := by sorry
