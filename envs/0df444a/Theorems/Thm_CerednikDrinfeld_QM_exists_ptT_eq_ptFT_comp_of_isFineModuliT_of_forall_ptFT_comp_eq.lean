-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_ptT_eq_ptFT_comp_of_isFineModuliT_of_forall_ptFT_comp_eq
-- name    : CerednikDrinfeld.QM.exists_ptT_eq_ptFT_comp_of_isFineModuliT_of_forall_ptFT_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/229112e3-288d-5fcf-ac5a-0ae5c6cdca03
-- title:
--   Descent of the moduli rule from triples to pairs along π
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, natural numbers $N,n,\ell$ and a commutative ring $\mathcal{O}$ in which $n$ is a unit. Let $f_{M_\ell} : M_\ell \to \operatorname{Spec}\mathcal{O}$ be a scheme over $\mathcal{O}$ together with a rule `ptFℓ` sending each commutative ring $S$, each morphism $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$, each pair $(E,P)$ consisting of a fake elliptic curve over $S$ with $\Lambda$-action and level-$N$ datum and a full level-$n$ structure $P$ on it, and each extra level-$\ell$ structure $K$ on $E$ (a closed subscheme of $E$, stable under the group law, inverse and the $\Lambda$-action, killed by $\ell$, disjoint from the level datum, finite flat of finite presentation of rank $\ell^2$ with geometric fibres isomorphic to $(\mathbb{Z}/\ell)^2$) to a morphism $\operatorname{Spec} S \to M_\ell$ over $s$; assume `IsFineModuliT Λ N n ℓ Mℓ fMℓ ptFℓ`, i.e. `ptFℓ` is invariant under isomorphisms of such triples, compatible with pullback along ring maps, and surjective and injective (up to isomorphism of triples) on $S$-points over $s$. Let $\pi_Y : Y \to \operatorname{Spec}\mathcal{O}$ and $\pi : M_\ell \to Y$ satisfy $\pi$ followed by $\pi_Y$ equals $f_{M_\ell}$. Assume further: (i) for all $S$, $s$, $E$, $K$ and all full level-$n$ structures $P,P'$ on $E$, the composites of `ptFℓ S s ⟨E, P'⟩ K` and `ptFℓ S s ⟨E, P⟩ K` with $\pi$ agree; and (ii) for every $S$ with $n$ a unit in $S$ and every pair $u=(E,K)$ over $S$ there exist a commutative ring $S'$ and $\varphi : S \to S'$ with $\operatorname{Spec}\varphi$ flat and surjective, a full level-$n$ triple $w'$ over $S'$ and an extra level $K'$ on $w'.1$ such that $u$ pulls back along $\varphi$ to $(w'.1,K')$ in the sense of `FakeEllipticCurve.WithExtraLevel.IsPullback` (a pullback square of the abelian schemes compatible with group law, $\Lambda$-action and both level subschemes). Then there is a rule `ptT` sending $S$, $s$ and a pair $(E,K)$ over $S$ to a morphism $\operatorname{Spec} S \to Y$ over $\pi_Y$ such that `ptT` is invariant under isomorphisms of pairs, is compatible with base change (if $\operatorname{Spec}\varphi$ followed by $s$ is $s'$ and $u$ pulls back to $u'$ along $\varphi$, then `ptT S' s' u'` is $\operatorname{Spec}\varphi$ followed by `ptT S s u`), and satisfies `ptT S s ⟨w.1, K⟩` $=$ `ptFℓ S s w K` followed by $\pi$ for every full level-$n$ triple $(w,K)$.
--
--   This is the descent step which forgets the auxiliary full level-$n$ structure: a rule on triples (fake elliptic curve, full level $n$, extra level $\ell$) valued in the fine moduli scheme $M_\ell$, once composed with a morphism $\pi$ that is insensitive to the full level, descends to a rule on pairs (fake elliptic curve, extra level $\ell$) valued in the target $Y$, using that pairs acquire full level structures after a flat surjective base change. It is used by [`CerednikDrinfeld.QM.IsFineModuliT.exists_isCoarseModuliT_of_quotient`](thm.html#CerednikDrinfeld.QM.IsFineModuliT.exists_isCoarseModuliT_of_quotient) to exhibit the quotient of $M_\ell$ as a coarse moduli space for pairs in the Čerednik–Drinfel'd setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_ptT_eq_ptFT_comp_of_isFineModuliT_of_forall_ptFT_comp_eq.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.exists_ptT_eq_ptFT_comp_of_isFineModuliT_of_forall_ptFT_comp_eq
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N n ℓ : ℕ) {𝒪 : Type} [CommRing 𝒪] (hn𝒪 : IsUnit ((n : ℕ) : 𝒪))
    (Mℓ : Scheme.{0}) (fMℓ : Mℓ ⟶ Spec (CommRingCat.of 𝒪))
    (ptFℓ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : FakeEllipticCurve.WithFullLevel Λ N n S), u.1.ExtraLevel ℓ → SchemeHomOver s fMℓ)
    (hMℓ : IsFineModuliT Λ N n ℓ Mℓ fMℓ ptFℓ)
    (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of 𝒪)) (π : Mℓ ⟶ Y) (hπ : π ≫ πY = fMℓ)

    (hinvP : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (E : FakeEllipticCurve Λ N S) (K : E.ExtraLevel ℓ) (P P' : E.FullLevel n),
      (ptFℓ S s ⟨E, P'⟩ K).1 ≫ π = (ptFℓ S s ⟨E, P⟩ K).1 ≫ π)

    (hloc : ∀ (S : Type) [CommRing S] (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), IsUnit ((n : ℕ) : S) →
      ∃ (S' : Type) (_ : CommRing S') (φ : S →+* S'),
        Flat (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) ∧
        ∃ (w' : FakeEllipticCurve.WithFullLevel Λ N n S') (K' : w'.1.ExtraLevel ℓ),
          FakeEllipticCurve.WithExtraLevel.IsPullback φ u ⟨w'.1, K'⟩) :
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
        (w : FakeEllipticCurve.WithFullLevel Λ N n S) (K : w.1.ExtraLevel ℓ), (ptT S s ⟨w.1, K⟩).1 = (ptFℓ S s w K).1 ≫ π) := by sorry
