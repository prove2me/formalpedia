-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuliT_exists_iso_comp_eq_of_isCoarseModuliT
-- name    : CerednikDrinfeld.QM.IsCoarseModuliT.exists_iso_comp_eq_of_isCoarseModuliT
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/647d3335-a2a4-59b1-8cf7-9bd7b214b0dc
-- title:
--   Uniqueness of the coarse moduli scheme with extra level ℓ
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, natural numbers $N,\ell$, and a commutative ring $B$. Let $X$ be a scheme with a morphism $\pi_X : X \to \operatorname{Spec} B$, together with a point rule $\mathrm{pt}$ assigning to every commutative ring $S$, every morphism $s : \operatorname{Spec} S \to \operatorname{Spec} B$ and every object of `FakeEllipticCurve.WithExtraLevel` $\Lambda\,N\,\ell\,S$ — a fake elliptic curve over $S$ with commutative relative group law, abelian-scheme property bundle, two-dimensional fibres, $\Lambda$-action satisfying the trace condition, level-$N$ data, plus an extra level-$\ell$ structure given by a closed immersion $K \to E.A$ which is a finite flat $\Lambda$-stable subgroup of $\ell$-torsion of rank $\ell^2$, disjoint from the level-$N$ subscheme, with $(\mathbb{Z}/\ell)^2$ geometric fibres — a morphism $\operatorname{Spec} S \to X$ whose composite with $\pi_X$ is $s$. Let $(X',\pi_{X'},\mathrm{pt}')$ be a second such datum. Assume both satisfy `IsCoarseModuliT`: the point rule is invariant under isomorphism of objects, compatible with base change along ring maps and pullback of objects, surjective and injective up to isomorphism on points valued in algebraically closed fields, and universal, in the sense that any other point rule over $\operatorname{Spec} B$ with the first two properties factors through it by a unique morphism over $\operatorname{Spec} B$. The conclusion is that there exists an isomorphism of schemes $i : X \cong X'$ with $i$ followed by $\pi_{X'}$ equal to $\pi_X$, such that for all $S$, $s$ and every object $E$ of `FakeEllipticCurve.WithExtraLevel` $\Lambda\,N\,\ell\,S$, the morphism $\mathrm{pt}'(S,s,E)$ equals $\mathrm{pt}(S,s,E)$ followed by $i$.
--
--   This is the standard uniqueness statement for a coarse moduli space: the coarse moduli scheme over $\operatorname{Spec} B$ for fake elliptic curves with $\Lambda$-action, level $N$ and extra level $\ell$ is unique up to a unique isomorphism over the base compatible with the point rules. It is used when comparing a coarse moduli scheme obtained as a quotient of a fine one with an independently constructed model, and in the transfer of geometric properties along the Čerednik–Drinfeld comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCoarseModuliT_exists_iso_comp_eq_of_isCoarseModuliT.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian
open scoped Quaternion

theorem CerednikDrinfeld.QM.IsCoarseModuliT.exists_iso_comp_eq_of_isCoarseModuliT
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ) {B : Type} [CommRing B]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of B))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)), FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πX)
    (hX : IsCoarseModuliT Λ N ℓ X πX pt)
    (X' : Scheme.{0}) (πX' : X' ⟶ Spec (CommRingCat.of B))
    (pt' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)), FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πX')
    (hX' : IsCoarseModuliT Λ N ℓ X' πX' pt') :
    ∃ i : X ≅ X', i.hom ≫ πX' = πX ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (E : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
        (pt' S s E).1 = (pt S s E).1 ≫ i.hom := by sorry
