-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuliT_exists_iso_of_isFineModuliT
-- name    : CerednikDrinfeld.QM.IsFineModuliT.exists_iso_of_isFineModuliT
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/9d88cea9-1455-50f8-8be7-321a2f7c236e
-- title:
--   Uniqueness of the fine moduli scheme of triples
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, natural numbers $N$, $n$, $\ell$ and a commutative ring $B$. Consider two schemes $M_\ell$, $M_\ell'$ equipped with morphisms $\pi_{M_\ell}\colon M_\ell\to\operatorname{Spec} B$ and $\pi_{M_\ell'}\colon M_\ell'\to\operatorname{Spec} B$, together with point rules $\mathrm{ptF}_\ell$, $\mathrm{ptF}_\ell'$ which assign, to every commutative ring $S$, every morphism $s\colon\operatorname{Spec} S\to\operatorname{Spec} B$, every pair $u=(E,P)$ consisting of a fake elliptic curve $E$ over $S$ with $\Lambda$-action and level-$N$ data and a full level-$n$ structure $P$ on it, and every extra level-$\ell$ structure $C$ on $E$ (a finite flat closed subscheme $C.K\hookrightarrow E.A$ of rank $\ell^2$, stable under the group law and the $\Lambda$-action, killed by $\ell$, disjoint from $E.\mathrm{lev}$, with geometric fibres isomorphic to $(\mathbb{Z}/\ell)^2$), a morphism $\operatorname{Spec} S\to M_\ell$ respectively $\operatorname{Spec} S\to M_\ell'$ whose composite with the structure morphism is $s$. Assume both triples of data satisfy `IsFineModuliT` for $(\Lambda,N,n,\ell)$: each point rule is constant on triples identified by an isomorphism in the sense of `WithFullLevel.IsoTVia`, is compatible with base change along ring homomorphisms through pullback comparison morphisms, is surjective onto the $S$-points over $s$, and identifies two triples only when they are so isomorphic. The conclusion is that there is an isomorphism of schemes $e\colon M_\ell\cong M_\ell'$ with $e$ followed by $\pi_{M_\ell'}$ equal to $\pi_{M_\ell}$, such that for all $S$, $s$, $u$ and $C$ the moduli point $\mathrm{ptF}_\ell(S,s,u,C)$ followed by $e$ equals $\mathrm{ptF}_\ell'(S,s,u,C)$, and $e$ is the unique morphism $M_\ell\to M_\ell'$ over $\operatorname{Spec} B$ with this last property.
--
--   This is the usual uniqueness, up to unique compatible isomorphism, of a scheme finely representing a moduli problem — here the problem of fake elliptic curves with full level-$n$ and extra level-$\ell$ structure over a base ring $B$. It is used to transport properties proved for one such model to any other, in particular in the comparison of the fine moduli scheme of triples with a coarse moduli scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuliT_exists_iso_of_isFineModuliT.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuliT

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsFineModuliT.exists_iso_of_isFineModuliT
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N n ℓ : ℕ) {B : Type} [CommRing B]
    {Mℓ : Scheme.{0}} {πMℓ : Mℓ ⟶ Spec (CommRingCat.of B)}
    {ptFℓ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (u : FakeEllipticCurve.WithFullLevel Λ N n S), u.1.ExtraLevel ℓ → SchemeHomOver s πMℓ}
    (hMℓ : IsFineModuliT Λ N n ℓ Mℓ πMℓ ptFℓ)
    {Mℓ' : Scheme.{0}} {πMℓ' : Mℓ' ⟶ Spec (CommRingCat.of B)}
    {ptFℓ' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (u : FakeEllipticCurve.WithFullLevel Λ N n S), u.1.ExtraLevel ℓ → SchemeHomOver s πMℓ'}
    (hMℓ' : IsFineModuliT Λ N n ℓ Mℓ' πMℓ' ptFℓ') :
    ∃ e : Mℓ ≅ Mℓ', e.hom ≫ πMℓ' = πMℓ ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
        (u : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel ℓ),
        (ptFℓ S s u C).1 ≫ e.hom = (ptFℓ' S s u C).1) ∧
      (∀ g : Mℓ ⟶ Mℓ', g ≫ πMℓ' = πMℓ →
        (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
          (u : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel ℓ),
          (ptFℓ S s u C).1 ≫ g = (ptFℓ' S s u C).1) → g = e.hom) := by sorry
