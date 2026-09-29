-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_P_eq_mapPt
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_P_eq_mapPt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/82301538-f36c-5a52-8539-228bc725570d
-- title:
--   Transport of a full level-m structure along an equivariant isomorphism
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, natural numbers $N$, $N'$, $m$, and a commutative ring $S$. Let $E$ be a fake elliptic curve of type $(\Lambda,N)$ over $S$ and $E'$ one of type $(\Lambda,N')$ over $S$; each carries a scheme $A$, a structure morphism $f$ to $\operatorname{Spec} S$, a relative group law $L$ on $T$-points over $\operatorname{Spec} S$, and an action `act` of $\Lambda$ by endomorphisms over $\operatorname{Spec} S$. Let $e$ be an isomorphism $E.A \cong E'.A$ with $e.\mathrm{hom}$ followed by $E'.f$ equal to $E.f$, so that post-composition with $e.\mathrm{hom}$ gives a map `mapPt` on points over any base $t : T \to \operatorname{Spec} S$. Assume this map is multiplicative for the two group laws, for every $T$, every $t$ and all points $P,Q$, and that $e.\mathrm{hom}$ intertwines the actions: $E.\mathrm{act}\,x$ followed by $e.\mathrm{hom}$ equals $e.\mathrm{hom}$ followed by $E'.\mathrm{act}\,x$ for each $x \in \Lambda$. Then for every full level-$m$ structure $P$ on $E$ — a section over the identity of $\operatorname{Spec} S$ that is killed by $m$ for $L$, whose specialisation at each geometric point $\operatorname{Spec} k \to \operatorname{Spec} S$ with $k$ algebraically closed generates all $m$-torsion points under the $\Lambda$-action, and whose annihilator in $\Lambda$ at each such point is exactly $m\Lambda$ — there exists a full level-$m$ structure $P'$ on $E'$ whose underlying section is the image of $P$'s section under `mapPt`.
--
--   This is the transport of level structures along an isomorphism of fake elliptic curves that respects both the group law on points and the quaternionic action, the bookkeeping needed to move a level-$m$ datum between two slots of the moduli vocabulary (for instance between a curve of level $N$ and one of level $1$ with the same underlying abelian surface). It is used in the rigidification and fine-moduli steps of the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_P_eq_mapPt.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_P_eq_mapPt
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N N' : ℕ} {S : Type u} [CommRing S] {m : ℕ}
    (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N' S)
    (e : E.A ≅ E'.A) (he : e.hom ≫ E'.f = E.f)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt e.hom he (E.L.mul t P Q) = E'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    (hact : ∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ E'.act x)
    (P : E.FullLevel m) :
    ∃ P' : E'.FullLevel m, P'.P = mapPt e.hom he P.P := by sorry
