-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_iso_pullback_equivariant_of_isLevelTwistAction
-- name    : CerednikDrinfeld.QM.IsFineModuli.exists_iso_pullback_equivariant_of_isLevelTwistAction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/bc619756-e5f7-5c79-8862-5864e1f36ac5
-- title:
--   Fine moduli of fake elliptic curves: equivariant base change
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $q\in v$ or $q'\in v$; let $\Lambda$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, and $N,m$ naturals with $N \neq 0$ and $m \geq 3$. Let $i : B_0 \to \mathcal{O}$ be a ring homomorphism with $\operatorname{Spec}$ of $i$ flat and with $N$ and $m$ units in $B_0$. Suppose $\pi_{M_0} : M_0 \to \operatorname{Spec} B_0$ together with $\mathrm{ptF}_0$ is a fine moduli datum for fake elliptic curves with full level-$m$ structure, in the sense that $\mathrm{ptF}_0$ assigns to every $S$-valued point $s$ of the base and every such object over $S$ a section over $s$, invariantly under isomorphism, compatibly with pullback along ring maps, surjectively onto all sections, and injectively up to isomorphism; and likewise $\pi_M : M \to \operatorname{Spec}\mathcal{O}$ with $\mathrm{ptF}$. Let finite groups $G_0$ and $G$ act through $\rho_0$, $\rho$ with labels $\chi_0$, $\chi$ as level-twist actions: each automorphism lies over the base, twisting an object by the label $\chi(g)$ moves its universal point by $\rho(g)$, and the labels are multiplicative, surjective and injective modulo $m\Lambda$. Finally let $H$ be a finite group with injective homomorphisms $\varphi_0 : H \to G_0$, $\varphi : H \to G$ such that $\chi_0(\varphi_0 h) - \chi(\varphi h) \in m\Lambda$ for all $h$. Then there is an isomorphism $e$ from $M$ to the fibre product of $\pi_{M_0}$ with $\operatorname{Spec}$ of $i$ which lies over $\operatorname{Spec}\mathcal{O}$ (its composite with the second projection is $\pi_M$), which intertwines $\rho(\varphi h)$ with the base change of $\rho_0(\varphi_0 h)$ for every $h \in H$, and which carries universal points to universal points: for every ring $S$, every $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$ and every object $u$ over $S$, the section $\mathrm{ptF}(S,s,u)$ followed by $e$ and the first projection equals $\mathrm{ptF}_0(S, s \circ \operatorname{Spec}(i), u)$.
--
--   This is the representability (fine-level) half of the statement that quotients of quaternionic moduli schemes commute with flat base change: a scheme representing the functor of fake elliptic curves with full level-$m$ structure over $\mathcal{O}$ is canonically the base change of one over $B_0$, compatibly with the twisting actions of a common finite group $H$. It is used in the construction of the quotient models over $\mathcal{O}$ and in the properness statement for such models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_exists_iso_pullback_equivariant_of_isLevelTwistAction.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsFineModuli.exists_iso_pullback_equivariant_of_isLevelTwistAction
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
    (hlabel : ∀ h : H, ∃ y : ↥Λ, (χ₀ (φ₀ h) : ℍ[ℚ, a, b]) - (χ (φ h) : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])) :
    ∃ e : M ⟶ Limits.pullback πM₀ (Spec.map (CommRingCat.ofHom i)),
      IsIso e ∧ e ≫ Limits.pullback.snd πM₀ (Spec.map (CommRingCat.ofHom i)) = πM ∧
      (∀ h : H, (ρ (φ h)).hom ≫ e =
        e ≫ Limits.pullback.lift (Limits.pullback.fst πM₀ (Spec.map (CommRingCat.ofHom i)) ≫ (ρ₀ (φ₀ h)).hom)
              (Limits.pullback.snd πM₀ (Spec.map (CommRingCat.ofHom i)))
              (by rw [Category.assoc, hρ₀.over_base, Limits.pullback.condition])) ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N m S),
        (ptF S s u).1 ≫ e ≫ Limits.pullback.fst πM₀ (Spec.map (CommRingCat.ofHom i)) =
          (ptF₀ S (s ≫ Spec.map (CommRingCat.ofHom i)) u).1) := by sorry
