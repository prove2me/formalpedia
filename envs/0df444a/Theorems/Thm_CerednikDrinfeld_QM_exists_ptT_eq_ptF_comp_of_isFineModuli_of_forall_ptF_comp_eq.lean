-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_ptT_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq
-- name    : CerednikDrinfeld.QM.exists_ptT_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/93ea33f6-305f-5d71-82f1-0f6f3baa693b
-- title:
--   Descent of the point rule to pairs with extra level
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$, naturals $N,m,\ell$, a further submodule $L_0$, and a commutative ring $\mathcal{O}$ in which $m$ is a unit. Let $\pi_M : M \to \operatorname{Spec}\mathcal{O}$ be a scheme over $\mathcal{O}$ together with a rule $\mathrm{pt}_F$ sending each ring $S$, each $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$ and each pair $(E,P)$ of a fake elliptic curve over $S$ with level-$N$ datum and a full level-$m$ structure to a morphism $\operatorname{Spec} S \to M$ over $s$; assume `hM`, that $\mathrm{pt}_F$ is constant on isomorphism classes, compatible with base change along ring maps, and for each $(S,s)$ surjective onto the $s$-morphisms to $M$ and injective up to isomorphism. Let $\pi_Y : Y \to \operatorname{Spec}\mathcal{O}$ and $\pi : M \to Y$ satisfy $\pi$ followed by $\pi_Y$ equals $\pi_M$. Say that an extra level $K$ of level $\ell$ on $E$ is cut out by $L_0$ from a full level $P$ if for every algebraically closed field $k$, every $sk : S \to k$ and every $k$-point $Q$ of $E$ over $\mathrm{geomPoint}\,k\,sk$, $Q$ factors through $K.\mathrm{levK}$ exactly when $Q = x \cdot \bigl((m/\ell)\,P_{k,sk}\bigr)$ for some $x \in \Lambda$ with $x \in L_0$, where $m/\ell$ is natural division and $x$ acts through $E.\mathrm{act}$. The hypotheses are: `hinvP`, that if two full level-$m$ structures $P,P'$ on the same $E$ both cut out the same $K$ in this sense then $\mathrm{pt}_F(E,P')$ followed by $\pi$ equals $\mathrm{pt}_F(E,P)$ followed by $\pi$; and `hloc`, that every pair $(E,K)$ of a fake elliptic curve with extra level $\ell$ over a ring $S$ in which $m$ is a unit admits a ring map $\varphi : S \to S'$ with $\operatorname{Spec}\varphi$ flat and surjective, a full level-$m$ object $w'$ over $S'$ and an extra level $K'$ on $w'.1$, such that $(E,K)$ pulls back to $(w'.1,K')$ along $\varphi$ and $K'$ is cut out by $L_0$ from $w'.2$. The conclusion is the existence of a rule $\mathrm{pt}_T$ assigning to each $S$, each $s$ and each pair $(E,K)$ with extra level $\ell$ a morphism $\operatorname{Spec} S \to Y$ over $s$, which is constant on isomorphism classes of such pairs, satisfies $\mathrm{pt}_T(u') = \operatorname{Spec}\varphi$ followed by $\mathrm{pt}_T(u)$ whenever $u'$ is the pullback of $u$ along $\varphi$ and the base points match, and satisfies $\mathrm{pt}_T(E,K) = \mathrm{pt}_F(E,P)$ followed by $\pi$ whenever $K$ is cut out by $L_0$ from the full level $P$.
--
--   This is the descent step which transfers the point rule of the fine moduli problem for fake elliptic curves with full level $m$ to the coarser problem of pairs (curve, extra level of order $\ell$), the extra level being the one spanned by $L_0 \cdot (m/\ell) \cdot P$; the flat surjective covers provided by `hloc` make the rule well defined on all pairs. It feeds the construction of a coarse moduli scheme for the raised-level problem, [`CerednikDrinfeld.QM.IsFineModuli.exists_isCoarseModuliT_of_quotient_of_isIndefiniteRamifiedExactlyAt_of_isUnit_mem_iff`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_isCoarseModuliT_of_quotient_of_isIndefiniteRamifiedExactlyAt_of_isUnit_mem_iff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_ptT_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.exists_ptT_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N m ℓ : ℕ) (L₀ : Submodule ℤ ℍ[ℚ, a, b])
    {𝒪 : Type} [CommRing 𝒪] (hm𝒪 : IsUnit ((m : ℕ) : 𝒪))
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM)
    (hM : IsFineModuli Λ N m M πM ptF)
    (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of 𝒪)) (π : M ⟶ Y) (hπ : π ≫ πY = πM)

    (hinvP : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (E : FakeEllipticCurve Λ N S) (K : E.ExtraLevel ℓ) (P P' : E.FullLevel m),
      (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) E.f),
        FactorsThrough K.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
            pushPt (E.act x) (E.act_over x)
              (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) = Q) →
      (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) E.f),
        FactorsThrough K.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
            pushPt (E.act x) (E.act_over x)
              (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P'.P k sk)) = Q) →
      (ptF S s ⟨E, P'⟩).1 ≫ π = (ptF S s ⟨E, P⟩).1 ≫ π)

    (hloc : ∀ (S : Type) [CommRing S] (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), IsUnit ((m : ℕ) : S) →
      ∃ (S' : Type) (_ : CommRing S') (φ : S →+* S'),
        Flat (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) ∧
        ∃ (w' : FakeEllipticCurve.WithFullLevel Λ N m S') (K' : w'.1.ExtraLevel ℓ),
          FakeEllipticCurve.WithExtraLevel.IsPullback φ u ⟨w'.1, K'⟩ ∧
          ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k) (Q : SchemeHomOver (geomPoint k sk) w'.1.f),
        FactorsThrough K'.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
            pushPt (w'.1.act x) (w'.1.act_over x)
              (nsmulPt w'.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt w'.2.P k sk)) = Q) :
    ∃ ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
        FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πY,
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), FakeEllipticCurve.WithExtraLevel.Iso u u' → ptT S s u = ptT S s u') ∧
      (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
        Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
        ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'),
          FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' → (ptT S' s' u').1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptT S s u).1) ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (w : FakeEllipticCurve.WithFullLevel Λ N m S) (K : w.1.ExtraLevel ℓ),
        (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) w.1.f),
        FactorsThrough K.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧
            pushPt (w.1.act x) (w.1.act_over x)
              (nsmulPt w.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt w.2.P k sk)) = Q) →
        (ptT S s ⟨w.1, K⟩).1 = (ptF S s w).1 ≫ π) := by sorry
