-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_iso_quotient_pullback_of_flat_pointCompat
-- name    : CerednikDrinfeld.QM.IsFineModuli.exists_iso_quotient_pullback_of_flat_pointCompat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/852f5570-0893-51ca-b223-4d4edc707b27
-- title:
--   Flat base change of quotients, compatibly with moduli points
-- statement:
--   Fix distinct primes $q,q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0<a$ or $0<b$ and, for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$; let $\Lambda$ be a maximal order, $N,m$ naturals with $N\neq 0$ and $m\ge 3$, and $i:B_0\to\mathcal{O}$ a ring map whose induced morphism of spectra is flat, with $N$ and $m$ units in $B_0$. Assume $M_0\to\operatorname{Spec}B_0$ with $\mathrm{ptF}_0$ is a fine moduli scheme for fake elliptic curves with $\Lambda$-action, level $N$ and full level $m$ structure (the point assignment being isomorphism-invariant, compatible with pullback, surjective and injective up to isomorphism), carrying a level-twist action of a finite group $G_0$ with labels $\chi_0$ in $\Lambda$, and likewise $M\to\operatorname{Spec}\mathcal{O}$, $\mathrm{ptF}$, $G$, $\chi$. Let $H$ be a finite group with injective homomorphisms $\varphi_0:H\to G_0$, $\varphi:H\to G$ such that $\chi_0(\varphi_0 h)-\chi(\varphi h)\in m\Lambda$ for all $h$. Assume further $\pi_0:M_0\to X_0$ over $B_0$ and $\pi:M\to X$ over $\mathcal{O}$ are quotients by the respective $H$-actions in the following sense: each is compatible with the structure morphisms, $H$-invariant, integral, affine, surjective on points, its fibres are exactly the $H$-orbits, its maps on sections over every open are injective with image the $H$-invariants, and it is initial among $H$-invariant morphisms. Then there are morphisms $e_M:M\to M_0\times_{\operatorname{Spec}B_0}\operatorname{Spec}\mathcal{O}$ and $e:X\to X_0\times_{\operatorname{Spec}B_0}\operatorname{Spec}\mathcal{O}$, both isomorphisms, compatible with the second projections (so defined over $\mathcal{O}$), such that for every commutative ring $S$, every $s:\operatorname{Spec}S\to\operatorname{Spec}\mathcal{O}$ and every object $u$ with full level $m$ structure over $S$, the section $\mathrm{ptF}\,S\,s\,u$ followed by $e_M$ and the first projection equals $\mathrm{ptF}_0\,S\,(s\circ\operatorname{Spec}i)\,u$, and such that $e\circ\pi$ agrees with $(\pi_0\times\mathrm{id})\circ e_M$.
--
--   This is the statement that forming the quotient of the fine moduli scheme of fake elliptic curves with full level structure by a finite subgroup of the level-twisting group commutes with flat base change, in the refined form which also records that the comparison isomorphism on the fine level transports the universal moduli points and commutes with the quotient maps. It is used in the construction of coarse moduli schemes after base change, in particular by the statements producing coarse moduli (and their $T$-variants) over a new base under injectivity and invertibility hypotheses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_exists_iso_quotient_pullback_of_flat_pointCompat.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsFineModuli.exists_iso_quotient_pullback_of_flat_pointCompat
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
    ∃ (eM : M ⟶ Limits.pullback πM₀ (Spec.map (CommRingCat.ofHom i))) (e : X ⟶ Limits.pullback πX₀ (Spec.map (CommRingCat.ofHom i))),
      IsIso eM ∧ IsIso e ∧
      eM ≫ Limits.pullback.snd πM₀ (Spec.map (CommRingCat.ofHom i)) = πM ∧
      e ≫ Limits.pullback.snd πX₀ (Spec.map (CommRingCat.ofHom i)) = πX ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N m S),
        (ptF S s u).1 ≫ eM ≫ Limits.pullback.fst πM₀ (Spec.map (CommRingCat.ofHom i)) =
          (ptF₀ S (s ≫ Spec.map (CommRingCat.ofHom i)) u).1) ∧
      π ≫ e = eM ≫ Limits.pullback.lift (Limits.pullback.fst πM₀ (Spec.map (CommRingCat.ofHom i)) ≫ π₀)
        (Limits.pullback.snd πM₀ (Spec.map (CommRingCat.ofHom i))) (by rw [Category.assoc, hπX₀, Limits.pullback.condition]) := by sorry
