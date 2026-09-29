-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuliT_existsUnique_comp_eq_and_isIso
-- name    : CerednikDrinfeld.QM.IsCoarseModuliT.existsUnique_comp_eq_and_isIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/5b579602-9e73-5f27-b214-52b723a4bfd6
-- title:
--   Uniqueness of the coarse moduli scheme up to unique isomorphism
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, natural numbers $N,\ell$, and a commutative ring $B$. Consider two schemes $Y,Y'$ with structure morphisms $\pi_Y : Y \to \operatorname{Spec} B$, $\pi_{Y'} : Y' \to \operatorname{Spec} B$, each equipped with a point rule: for every commutative ring $S$, every $s : \operatorname{Spec} S \to \operatorname{Spec} B$ and every object $u$ of $\mathrm{WithExtraLevel}\ \Lambda\ N\ \ell\ S$ — that is, a fake elliptic curve over $S$ (an abelian scheme with commutative relative group law, two-dimensional fibres, a $\Lambda$-action with the prescribed trace condition and level-$N$ data) together with an extra level-$\ell$ structure, a closed subgroup scheme $K$ that is finite flat of rank $\ell^2$, killed by $\ell$, $\Lambda$-stable, disjoint from the level-$N$ subscheme and geometrically isomorphic to $(\mathbb{Z}/\ell)^2$ — a morphism $\operatorname{Spec} S \to Y$ (resp. $Y'$) over $s$. Assume both triples satisfy `IsCoarseModuliT`: isomorphism-invariance of the point rule, compatibility with pullback along ring maps, bijectivity on points over algebraically closed fields, and the universal property among all such point rules. Then there is exactly one $g : Y \to Y'$ with $g$ followed by $\pi_{Y'}$ equal to $\pi_Y$ and $(\mathrm{pt}'_{S,s}(u)).1 = (\mathrm{pt}_{S,s}(u)).1$ followed by $g$ for all $S,s,u$; moreover every such $g$ is an isomorphism.
--
--   This is the standard uniqueness statement for coarse moduli spaces, here for the moduli problem of fake elliptic curves with $\Lambda$-action, level $N$ and extra level $\ell$: any two coarse moduli schemes over the same base $B$ are identified by a unique point-compatible $B$-morphism. It is used to transfer properties (such as properness or integrality of fibres) between different constructions of the relevant Shimura curve and its integral models, and is invoked by the statements comparing coarse moduli schemes under base change and over algebraically closed fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCoarseModuliT_existsUnique_comp_eq_and_isIso.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.IsCoarseModuliT.existsUnique_comp_eq_and_isIso
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} {B : Type} [CommRing B]
    {Y : Scheme.{0}} {πY : Y ⟶ Spec (CommRingCat.of B)}
    {ptT : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πY}
    (hY : IsCoarseModuliT Λ N ℓ Y πY ptT)
    {Y' : Scheme.{0}} {πY' : Y' ⟶ Spec (CommRingCat.of B)}
    {ptT' : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithExtraLevel Λ N ℓ S → SchemeHomOver s πY'}
    (hY' : IsCoarseModuliT Λ N ℓ Y' πY' ptT') :
    (∃! g : Y ⟶ Y', g ≫ πY' = πY ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
        (ptT' S s u).1 = (ptT S s u).1 ≫ g) ∧
    ∀ g : Y ⟶ Y', g ≫ πY' = πY →
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S),
        (ptT' S s u).1 = (ptT S s u).1 ≫ g) → IsIso g := by sorry
