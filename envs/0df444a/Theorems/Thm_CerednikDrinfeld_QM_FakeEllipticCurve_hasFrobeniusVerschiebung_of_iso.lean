-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_hasFrobeniusVerschiebung_of_iso
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.hasFrobeniusVerschiebung_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/65fc754d-2a66-5106-99b8-953bd7e1d818
-- title:
--   Transport of Frobenius–Verschiebung data along an isomorphism
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a prime $\ell$, and a commutative ring $S$ of characteristic $\ell$. Let $d$, $d'$, $E$ be fake elliptic curves of type `FakeEllipticCurve Λ N S`, each consisting of a scheme over $\operatorname{Spec} S$ that is smooth, proper with connected fibres of Krull dimension $2$, equipped with a commutative relative group law on its functor of points, an action of $\Lambda$ by endomorphisms over $S$ compatible with the group law and with the trace condition, and a level structure $\mathrm{lev}$. Assume `HasFrobeniusVerschiebung ℓ d d'`, i.e. there exists a datum consisting of a morphism $\mathrm{pr} : d'.A \to d.A$ fitting into a pullback square over $\operatorname{Spec}$ of the $\ell$-power Frobenius of $S$ and compatible with the group laws, the $\Lambda$-actions and the level structures, together with morphisms $F : d.A \to d'.A$ and $V : d'.A \to d.A$ over $S$, each additive on $T$-points, commuting with the $\Lambda$-action, and preserving points factoring through the level structures, subject to further relations among $\mathrm{pr}$, $F$ and $V$. Assume moreover `FakeEllipticCurve.Iso d' E`: there is an isomorphism of schemes $e : d'.A \cong E.A$ over $S$ that transports the group laws on $T$-points, intertwines the $\Lambda$-actions, and matches factorisation through the respective level structures. Then `HasFrobeniusVerschiebung ℓ d E` holds.
--
--   This is a bookkeeping step in the characteristic-$\ell$ analysis of the Eichler–Shimura congruence for Shimura curves: the Frobenius twist of a fake elliptic curve is characterised only relationally, and isogeny-uniqueness arguments produce it merely up to isomorphism of fake elliptic curves, so a Frobenius–Verschiebung datum must be transportable along such an isomorphism. It is used in the derivation of `hasFrobeniusVerschiebung_of_isLevelIsogeny_of_exists_factorsThrough_ne_one`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_hasFrobeniusVerschiebung_of_iso.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.hasFrobeniusVerschiebung_of_iso
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S : Type u} [CommRing S] (ℓ : ℕ) [Fact ℓ.Prime] [CharP S ℓ]
    (d d' E : FakeEllipticCurve Λ N S)
    (hD : HasFrobeniusVerschiebung ℓ d d') (he : FakeEllipticCurve.Iso d' E) :
    HasFrobeniusVerschiebung ℓ d E := by sorry
