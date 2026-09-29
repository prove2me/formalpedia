-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuliT_ptFT_comp_eq_ptFT_comp_of_fullLevel
-- name    : CerednikDrinfeld.QM.IsFineModuliT.ptFT_comp_eq_ptFT_comp_of_fullLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/2ca11af4-9f16-54e0-b364-3eace920a80b
-- title:
--   Invariance of πcircpt_{F,ℓ} under change of full level
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$ which is an order (it contains $1$, is closed under multiplication, spans the quaternion algebra over $\mathbb{Q}$ and is finitely generated), naturals $N,n,\ell$, and a commutative ring $\mathcal{O}$ in which the image of $n$ is a unit. Let $f_{M_\ell}\colon M_\ell \to \operatorname{Spec}\mathcal{O}$ be a scheme over $\mathcal{O}$ together with an assignment $\mathrm{pt}_{F,\ell}$ sending each commutative ring $S$, each $s\colon \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$, each pair $u=(E,P)$ of a fake elliptic curve $E$ over $S$ with $\Lambda$-action and level-$N$ datum together with a full level-$n$ structure $P$ on $E$, and each extra level-$\ell$ structure on $E$, to a morphism $\operatorname{Spec} S \to M_\ell$ over $s$; assume `IsFineModuliT` for this datum, i.e. $\mathrm{pt}_{F,\ell}$ is constant on `IsoTVia`-isomorphism classes, compatible with base change along ring homomorphisms (under the stated pullback and level conditions), surjective onto the $S$-points of $M_\ell$ over $s$, and injective up to an `IsoTVia`-isomorphism. Let $G$ be a group with a homomorphism $\rho_\ell\colon G \to \operatorname{Aut} M_\ell$ and a labelling map $\chi\colon G \to \Lambda$ subject to two hypotheses: (i) for all $c,d \in \Lambda$ with $cd-1 \in n\Lambda$ and $dc-1 \in n\Lambda$ there are $h \in G$ and $y \in \Lambda$ with $\chi(h)-c = n\,y$, so every invertible class modulo $n\Lambda$ occurs as a label; (ii) for every $h \in G$, every $S$, every $s$, all $u,u'$ with full level-$n$ structures and extra level-$\ell$ structures $C,C'$, and every isomorphism $e\colon u_1.A \cong u'_1.A$ over $S$ which exhibits $u'$ as the $\chi(h)$-twist of $u$ (it is compatible with the relative group laws, intertwines the $\Lambda$-actions, matches the level-$N$ data under `FactorsThrough`, and carries $\chi(h)\cdot P$ to $P'$) and which also matches the extra levels, in the sense that a point $P$ over any $t\colon T \to \operatorname{Spec} S$ factors through $C.\mathtt{levK}$ if and only if its image under $e$ factors through $C'.\mathtt{levK}$, one has $\mathrm{pt}_{F,\ell}(S,s,u',C') = \mathrm{pt}_{F,\ell}(S,s,u,C)$ followed by $\rho_\ell(h)$. Let finally $\pi\colon M_\ell \to X$ satisfy $\rho_\ell(h)$ followed by $\pi$ equals $\pi$ for all $h \in G$. Then for every commutative ring $S$, every $s\colon \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$, every fake elliptic curve $E$ over $S$, every extra level-$\ell$ structure $K$ on $E$ and any two full level-$n$ structures $P,P'$ on $E$, the morphism $\mathrm{pt}_{F,\ell}(S,s,(E,P'),K)$ followed by $\pi$ equals $\mathrm{pt}_{F,\ell}(S,s,(E,P),K)$ followed by $\pi$.
--
--   This says that a $\rho_\ell$-invariant morphism out of the fine moduli scheme of triples (fake elliptic curve, full level-$n$ structure, extra level-$\ell$ structure) no longer sees the full level-$n$ structure, the labelling hypothesis supplying enough group elements to move one full level structure to another by a twist. It is the ingredient used by [`CerednikDrinfeld.QM.IsFineModuliT.exists_isCoarseModuliT_of_quotient`](thm.html#CerednikDrinfeld.QM.IsFineModuliT.exists_isCoarseModuliT_of_quotient) to descend the fine moduli problem with full level structure to a coarse moduli scheme for the problem without it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuliT_ptFT_comp_eq_ptFT_comp_of_fullLevel.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsFineModuliT.ptFT_comp_eq_ptFT_comp_of_fullLevel
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛord : IsOrder Λ) {N n ℓ : ℕ} {𝒪 : Type} [CommRing 𝒪]
    (hn' : IsUnit ((n : ℕ) : 𝒪))
    {Mℓ : Scheme.{0}} {fMℓ : Mℓ ⟶ Spec (CommRingCat.of 𝒪)}
    {ptFℓ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : FakeEllipticCurve.WithFullLevel Λ N n S), u.1.ExtraLevel ℓ → SchemeHomOver s fMℓ}
    (hMℓ : IsFineModuliT Λ N n ℓ Mℓ fMℓ ptFℓ)
    {G : Type} [Group G] (ρℓ : G →* Aut Mℓ) (χ : G → ↥Λ)

    (hlabel : ∀ c d : ↥Λ,
      (∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1 = (n : ℚ) • (y : ℍ[ℚ, a, b])) →
      (∃ y : ↥Λ, (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) - 1 = (n : ℚ) • (y : ℍ[ℚ, a, b])) →
        ∃ (h : G) (y : ↥Λ), (χ h : ℍ[ℚ, a, b]) - (c : ℍ[ℚ, a, b]) = (n : ℚ) • (y : ℍ[ℚ, a, b]))

    (hρℓtw : ∀ (h : G) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
          (u u' : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel ℓ) (C' : u'.1.ExtraLevel ℓ)
          (e : u.1.A ≅ u'.1.A) (he : e.hom ≫ u'.1.f = u.1.f),
          FakeEllipticCurve.WithFullLevel.IsTwistVia (χ h) u u' e he →
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
              FactorsThrough C.levK P ↔ FactorsThrough C'.levK (mapPt e.hom he P)) →
            (ptFℓ S s u' C').1 = (ptFℓ S s u C).1 ≫ (ρℓ h).hom)
    {X : Scheme.{0}} (π : Mℓ ⟶ X) (hπρ : ∀ h : G, (ρℓ h).hom ≫ π = π)
    (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
    (E : FakeEllipticCurve Λ N S) (K : E.ExtraLevel ℓ) (P P' : E.FullLevel n) :
    (ptFℓ S s ⟨E, P'⟩ K).1 ≫ π = (ptFℓ S s ⟨E, P⟩ K).1 ≫ π := by sorry
