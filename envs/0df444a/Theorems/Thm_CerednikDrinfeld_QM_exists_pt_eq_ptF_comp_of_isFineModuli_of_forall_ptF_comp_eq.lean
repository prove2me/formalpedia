-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_pt_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq
-- name    : CerednikDrinfeld.QM.exists_pt_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/0c744ba6-785c-5ff0-88bb-34dbc8a1776c
-- title:
--   Descent of the point map along the forgetful morphism
-- statement:
--   Fix $a,b\in\mathbb{Q}$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, and naturals $N,m$. Let $\mathcal{O}$ be a commutative ring in which the image of $m$ is a unit, let $\pi_M : M \to \operatorname{Spec}\mathcal{O}$ be a scheme over $\mathcal{O}$, and let $\mathrm{ptF}$ assign, to each commutative ring $S$, each morphism $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$ and each pair $(E,P)$ consisting of an object of `FakeEllipticCurve Λ N S` (an abelian scheme over $S$ with commutative relative group law, two-dimensional fibres, a $\Lambda$-action subject to additivity, multiplicativity and trace conditions, and level-$N$ data) together with a full level-$m$ structure $P$ on $E$ (a section killed by $m$ whose $\Lambda$-orbit exhausts the $m$-torsion at algebraically closed geometric points and whose annihilator in $\Lambda$ is $m\Lambda$), a morphism $\operatorname{Spec} S \to M$ over $s$; assume `IsFineModuli`, i.e. $\mathrm{ptF}$ is invariant under isomorphism of pairs, compatible with pullback along ring maps, surjective onto $S$-points of $M$ over $s$, and injective up to isomorphism. Let $\pi_X : X \to \operatorname{Spec}\mathcal{O}$ and $\pi : M \to X$ satisfy $\pi \circ \pi_X = \pi_M$. Assume (`hinvP`) that $\pi \circ \mathrm{ptF}(E,P)$ is independent of the full level-$m$ structure $P$ on a given $E$, and (`hloc`) that every fake elliptic curve $E$ over a ring $S$ in which $m$ is a unit admits a ring map $\varphi : S \to S'$ with $\operatorname{Spec}\varphi$ flat and surjective and a pair over $S'$ whose underlying curve is a pullback of $E$ along $\varphi$. Then there is a rule $\mathrm{pt}$ sending each $S$, each $s$ and each fake elliptic curve $E$ over $S$ to a morphism $\operatorname{Spec} S \to X$ over $s$ such that $\mathrm{pt}$ is constant on isomorphism classes, satisfies $\mathrm{pt}(E') = \operatorname{Spec}\varphi \circ \mathrm{pt}(E)$ whenever $E'$ is a pullback of $E$ along $\varphi$ and the base points match, and satisfies $\mathrm{pt}(E) = \pi \circ \mathrm{ptF}(E,P)$ for every pair $(E,P)$ with full level $m$. No uniqueness of $\mathrm{pt}$ is asserted.
--
--   This is the descent step that converts a fine moduli point map for fake elliptic curves with full level-$m$ structure into a point map for fake elliptic curves alone, by pushing forward along a morphism $\pi$ that forgets the full level structure and covering a general curve by one that carries such a structure after a flat surjective base change. It feeds the construction of coarse moduli schemes for quaternionic curves in [`CerednikDrinfeld.QM.IsFineModuli.exists_isCoarseModuli_of_quotient_of_isIndefiniteRamifiedExactlyAt`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_isCoarseModuli_of_quotient_of_isIndefiniteRamifiedExactlyAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_pt_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.exists_pt_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N m : ℕ) {𝒪 : Type} [CommRing 𝒪] (hm𝒪 : IsUnit ((m : ℕ) : 𝒪))
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM)
    (hM : IsFineModuli Λ N m M πM ptF)
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of 𝒪)) (π : M ⟶ X) (hπ : π ≫ πX = πM)

    (hinvP : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (E : FakeEllipticCurve Λ N S) (P P' : E.FullLevel m), (ptF S s ⟨E, P'⟩).1 ≫ π = (ptF S s ⟨E, P⟩).1 ≫ π)

    (hloc : ∀ (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S), IsUnit ((m : ℕ) : S) →
      ∃ (S' : Type) (_ : CommRing S') (φ : S →+* S'),
        Flat (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) ∧
        ∃ u' : FakeEllipticCurve.WithFullLevel Λ N m S', FakeEllipticCurve.IsPullback φ E u'.1) :
    ∃ pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
        FakeEllipticCurve Λ N S → SchemeHomOver s πX,
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (E E' : FakeEllipticCurve Λ N S), FakeEllipticCurve.Iso E E' → pt S s E = pt S s E') ∧
      (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
        Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
        ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
          FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1) ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (w : FakeEllipticCurve.WithFullLevel Λ N m S), (pt S s w.1).1 = (ptF S s w).1 ≫ π) := by sorry
