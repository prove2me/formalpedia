-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isPullback_of_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_isPullback_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/3d6f5da9-eaad-56b7-a003-8e1be0327ee1
-- title:
--   Pull-backs of a fake elliptic curve with extra level are unique
-- statement:
--   Let $a,b\in\mathbb{Q}$, let $\Lambda$ be a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, let $N,\ell$ be natural numbers, let $S,S'$ be commutative rings and let $\varphi : S \to S'$ be a ring homomorphism. Let $u$ be a fake elliptic curve of level data $(\Lambda,N)$ over $S$ together with an extra level structure at $\ell$ (a pair consisting of $E$ and an `ExtraLevel` datum, whose subscheme is $u.2.K$ with immersion $u.2.levK$), and let $u',u''$ be two such objects over $S'$. Assume that each of $u'$ and $u''$ is a pull-back of $u$ along $\varphi$, in the sense that there is a morphism $g$ from its total space to $u.1.A$ making the square with the structure morphisms and $\mathrm{Spec}\,\varphi$ cartesian, such that $g$ carries the relative group law on points over $\mathrm{Spec}\,S'$ to that over $\mathrm{Spec}\,S$, satisfies $u'.1.act\,x \mathbin{\text{then}} g = g \mathbin{\text{then}} u.1.act\,x$ for all $x\in\Lambda$, and sends any point factoring through the level structure $u'.1.lev$ (respectively through $u'.2.levK$) to a point factoring through $u.1.lev$ (respectively $u.2.levK$) after composition with $g$. Then $u'$ and $u''$ are isomorphic: there is an isomorphism $e$ of total spaces over $\mathrm{Spec}\,S'$ which is compatible with the group laws on points, commutes with the $\Lambda$-actions, and for which a point factors through $u'.1.lev$ (respectively $u'.2.levK$) if and only if its image factors through $u''.1.lev$ (respectively $u''.2.levK$).
--
--   This is the uniqueness clause for base change in the moduli problem of fake elliptic curves with $\Gamma$-level and an auxiliary level structure at $\ell$, in the Čerednik–Drinfeld setting: a pull-back along a ring map is determined up to isomorphism of the whole datum, not merely of the underlying abelian scheme. It is used in the comparison of points of fine moduli schemes under base change, namely in [`CerednikDrinfeld.QM.exists_ptT_eq_ptFT_comp_of_isFineModuliT_of_forall_ptFT_comp_eq`](thm.html#CerednikDrinfeld.QM.exists_ptT_eq_ptFT_comp_of_isFineModuliT_of_forall_ptFT_comp_eq) and [`CerednikDrinfeld.QM.exists_ptT_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq`](thm.html#CerednikDrinfeld.QM.exists_ptT_eq_ptF_comp_of_isFineModuli_of_forall_ptF_comp_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_of_isPullback_of_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_of_isPullback_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (u' u'' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S')
    (h' : FakeEllipticCurve.WithExtraLevel.IsPullback φ u u') (h'' : FakeEllipticCurve.WithExtraLevel.IsPullback φ u u'') :
    FakeEllipticCurve.WithExtraLevel.Iso u' u'' := by sorry
