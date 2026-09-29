-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_flat_and_locallyOfFiniteType_of_quotient_of_isUnit_two_of_isUnit_three
-- name    : CerednikDrinfeld.QM.IsFineModuli.flat_and_locallyOfFiniteType_of_quotient_of_isUnit_two_of_isUnit_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/07323976-114d-5b6b-8f97-0c350fa32411
-- title:
--   Finite quotient of the fine moduli scheme is flat, locally of finite type
-- statement:
--   Let $q \neq q'$ be primes and $a,b \in \mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathbb{Q}$ the completion $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $q$ or $q'$ lies in $v$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order maximal among orders containing it, let $N \geq 1$ and $m \geq 3$, and let $\mathcal{O}$ be a domain of characteristic zero in which $N$, $m$, $2$ and $3$ are units. Let $\pi_M : M \to \operatorname{Spec}\mathcal{O}$ be a scheme over $\mathcal{O}$ together with an assignment $\mathrm{ptF}$ sending each commutative ring $S$, each morphism $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$ and each pair consisting of a fake elliptic curve over $S$ with $\Lambda$-action and level-$N$ data together with a full level-$m$ structure, to a section of $\pi_M$ over $s$; the hypothesis `IsFineModuli` says that $\mathrm{ptF}$ is constant on isomorphism classes, compatible with base change along ring maps (matching pullbacks of the data to composition of sections with $\operatorname{Spec}$ of the map), surjective onto all such sections, and injective up to isomorphism of the data. Let $\rho : G \to \operatorname{Aut} M$ be an action of a finite group with labels $\chi : G \to \Lambda$ satisfying `IsLevelTwistAction`: each $\rho(g)$ lies over $\operatorname{Spec}\mathcal{O}$, twisting the data by $\chi(g)$ corresponds to composing the $\mathrm{ptF}$-section with $\rho(g)$, and $\chi$ is multiplicative, unital, surjective onto invertible classes and injective modulo $m\Lambda$. Let $\varphi : H \to G$ be an injective homomorphism of a finite group $H$, and let $\pi : M \to X$, $\pi_X : X \to \operatorname{Spec}\mathcal{O}$ satisfy $\pi$ followed by $\pi_X$ equals $\pi_M$ and exhibit $X$ as a quotient of $M$ by $H$ acting through $\rho \circ \varphi$: $\pi$ is invariant under each $\rho(\varphi(h))$, integral, affine and surjective on points, its point fibres are exactly the $H$-orbits, each $\pi.\mathrm{app}\,V$ is injective with image the $H$-invariant sections, every $H$-invariant affine open of $M$ is the preimage of an affine open of $X$, and $\pi$ is universal among $H$-invariant morphisms out of $M$. Then $\pi_X$ is flat and locally of finite type.
--
--   This supplies the two base properties — flatness and local finiteness of type over the base ring — for the quotients of the fine moduli scheme of fake elliptic curves with full level structure which serve as models of quaternionic Shimura curves over an arbitrary characteristic-zero domain with $6$ invertible. It is used in establishing integrality and properness of the coarse moduli schemes built from these quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_flat_and_locallyOfFiniteType_of_quotient_of_isUnit_two_of_isUnit_three.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsFineModuli.flat_and_locallyOfFiniteType_of_quotient_of_isUnit_two_of_isUnit_three
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q) {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N m : ℕ) [NeZero N] (hm : 3 ≤ m)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hN : IsUnit ((N : ℕ) : 𝒪)) (hm' : IsUnit ((m : ℕ) : 𝒪))
    (h2 : IsUnit ((2 : ℕ) : 𝒪)) (h3 : IsUnit ((3 : ℕ) : 𝒪))
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N m M πM ptF)
    {G : Type} [Group G] [Finite G] {ρ : G →* Aut M} {χ : G → ↥Λ} (hρ : IsLevelTwistAction Λ N m M πM ptF G ρ χ)
    (H : Type) [Group H] [Finite H] (φ : H →* G) (hφ : Function.Injective φ)
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of 𝒪)) (π : M ⟶ X) (hπX : π ≫ πX = πM)
    (hπ : ∀ h : H, (ρ (φ h)).hom ≫ π = π)
    (hint : IsIntegralHom π) (haff : IsAffineHom π) (hsurj : Function.Surjective π.base)
    (horbit : ∀ x x' : M, π.base x = π.base x' ↔ ∃ h : H, (ρ (φ h)).hom.base x = x')
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ h : H, (ρ (φ h)).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s})
    (hopen : ∀ U : M.Opens, IsAffineOpen U → (∀ h : H, (ρ (φ h)).hom ⁻¹ᵁ U = U) → ∃ V : X.Opens, IsAffineOpen V ∧ π ⁻¹ᵁ V = U)
    (hcat : ∀ (T : Scheme.{0}) (f : M ⟶ T), (∀ h : H, (ρ (φ h)).hom ≫ f = f) → ∃! f' : X ⟶ T, π ≫ f' = f) :
    Flat πX ∧ LocallyOfFiniteType πX := by sorry
