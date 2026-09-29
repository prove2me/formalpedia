-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuliT_existsUnique_hom_ptFT_comp_eq
-- name    : CerednikDrinfeld.QM.IsFineModuliT.existsUnique_hom_ptFT_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/2a43723f-10cb-5fda-b787-56955a2d6e6f
-- title:
--   Morphisms out of the fine moduli scheme of triples
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, natural numbers $N,n,\ell$ and a commutative ring $\mathcal{O}$. Let $f_{M_\ell} : M_\ell \to \operatorname{Spec}\mathcal{O}$ be a scheme over $\mathcal{O}$, and let $\mathrm{pt}_{F,\ell}$ assign, to every commutative ring $S$, every morphism $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$, every pair $u=(E,P)$ consisting of a fake elliptic curve $E$ over $S$ for $(\Lambda,N)$ together with a structure of type `FullLevel n` on $E$, and every `ExtraLevel` $\ell$ structure $C$ on $E$ (a closed subscheme $K \subseteq E$, stable under the group law, inversion and the $\Lambda$-action, killed by $\ell$, meeting the level-$N$ structure only in the identity, finite flat of finite presentation with fibre rank $\ell^2$ and geometric fibres isomorphic to $(\mathbb{Z}/\ell)^2$), a morphism $\operatorname{Spec} S \to M_\ell$ whose composite with $f_{M_\ell}$ is $s$. Assume `IsFineModuliT` for these data: $\mathrm{pt}_{F,\ell}$ is invariant under isomorphisms of triples in the sense of `IsoTVia`, compatible with pullback of triples along ring homomorphisms, surjective onto such points, and injective up to such isomorphism. Let further $\pi_T : T \to \operatorname{Spec}\mathcal{O}$ be a scheme over $\mathcal{O}$ and let $\mathrm{pt}'$ assign to each pair $(E,C)$ over $S$ a point of $T$ over $s$, with $\mathrm{pt}'$ constant on `WithExtraLevel.Iso`-classes and satisfying $(\mathrm{pt}'_{S'}(u'))_1 = \operatorname{Spec}(\varphi) \circ (\mathrm{pt}'_S(u))_1$ whenever $u'$ is a pullback of $u$ along $\varphi : S \to S'$ in the sense of `WithExtraLevel.IsPullback`. Then there is exactly one $\Phi : M_\ell \to T$ with $\Phi$ followed by $\pi_T$ equal to $f_{M_\ell}$ and $(\mathrm{pt}'_S(E,C))_1 = (\mathrm{pt}_{F,\ell}(E,P,C))_1$ followed by $\Phi$ for all $S$, $s$, $(E,P)$ and $C$.
--
--   This is the corepresentability (Yoneda) property of the fine moduli scheme of triples $(E,P,K)$: any rule on pairs $(E,K)$ that is isomorphism-invariant and compatible with base change factors uniquely through $M_\ell$ by a morphism over $\mathcal{O}$. It is used in the comparison of $M_\ell$ with coarse moduli data: in the construction of a coarse moduli scheme from a quotient, in the identification of that quotient with the coarse space, and in the finiteness and surjectivity statement for the resulting map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuliT_existsUnique_hom_ptFT_comp_eq.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsFineModuliT.existsUnique_hom_ptFT_comp_eq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N n ℓ : ℕ} {𝒪 : Type} [CommRing 𝒪]
    {Mℓ : Scheme.{0}} {fMℓ : Mℓ ⟶ Spec (CommRingCat.of 𝒪)}
    {ptFℓ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : FakeEllipticCurve.WithFullLevel Λ N n S), u.1.ExtraLevel ℓ → SchemeHomOver s fMℓ}
    (hMℓ : IsFineModuliT Λ N n ℓ Mℓ fMℓ ptFℓ)
    (T : Scheme.{0}) (πT : T ⟶ Spec (CommRingCat.of 𝒪))
    (pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
        FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πT)
    (hiso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S), FakeEllipticCurve.WithExtraLevel.Iso u u' → pt' S s u = pt' S s u')
    (hpb : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
      ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S'),
        FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' → (pt' S' s' u').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt' S s u).1) :
    ∃! Φ : Mℓ ⟶ T, Φ ≫ πT = fMℓ ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (u : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel ℓ), (pt' S s ⟨u.1, C⟩).1 = (ptFℓ S s u C).1 ≫ Φ := by sorry
