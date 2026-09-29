-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_extraLevel_isoTVia_of_isoVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_extraLevel_isoTVia_of_isoVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/c14b9db3-d757-5037-94fc-499d86312e49
-- title:
--   Extra level structures transport along an isomorphism of pairs
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, natural numbers $N,m$ and a commutative ring $S$. Let $u,u'$ be elements of `FakeEllipticCurve.WithFullLevel Λ N m S`, that is, pairs consisting of a fake elliptic curve over $S$ with $\Lambda$-action and level datum (an abelian scheme $f : A \to \operatorname{Spec} S$ with commutative relative group law $L$, two-dimensional fibres, an action of $\Lambda$ over $S$ with the prescribed trace condition, and a level subscheme `lev`) together with a full level-$m$ structure on it (a point $P$ over $\operatorname{Spec} S$ that is $m$-torsion, whose $\Lambda$-translates exhaust the geometric $m$-torsion, and whose annihilator in $\Lambda$ is $m\Lambda$). Let $e$ be an isomorphism of the underlying schemes $u.1.A \cong u'.1.A$ with $e.\mathrm{hom}$ followed by $u'.1.f$ equal to $u.1.f$, and assume `IsoVia u u' e he`: composition with $e.\mathrm{hom}$ is a homomorphism for the two group laws on $T$-points for every $t : T \to \operatorname{Spec} S$, it intertwines the $\Lambda$-actions ($u.1.\mathrm{act}\,x$ followed by $e.\mathrm{hom}$ equals $e.\mathrm{hom}$ followed by $u'.1.\mathrm{act}\,x$), a $T$-point factors through $u.1.\mathrm{lev}$ exactly when its image factors through $u'.1.\mathrm{lev}$, and it carries $u.2.P$ to $u'.2.P$. Then for every natural number $\ell$ and every extra level structure $C'$ of level $\ell$ on $u'.1$ (a closed immersion $\mathrm{lev}K : K \to u'.1.A$ whose points form a $\Lambda$-stable $\ell$-torsion subgroup meeting the level subscheme only in the unit, finite, flat and of locally finite presentation over $S$ of fibre rank $\ell^2$, with geometric fibres isomorphic as groups to $\mathbb{Z}/\ell \times \mathbb{Z}/\ell$ where $\ell$ is invertible) there exists an extra level structure $C$ of level $\ell$ on $u.1$ with `IsoTVia u u' C C' e he`, i.e. `IsoVia u u' e he` together with: for every $t : T \to \operatorname{Spec} S$ and every $T$-point $P$ of $u.1.f$, $P$ factors through $C.\mathrm{lev}K$ if and only if $P$ followed by $e.\mathrm{hom}$ factors through $C'.\mathrm{lev}K$.
--
--   This is the transport of an auxiliary $\ell$-level structure (a subgroup scheme of type $(\mathbb{Z}/\ell)^2$ disjoint from the given level datum) across an isomorphism of fake elliptic curves with full level structure, in the form needed when the moduli problem with extra level is compared with the one without. It is used in the fine-moduli argument [`CerednikDrinfeld.QM.IsFineModuliT.ext_of_comp_forget_eq_of_specMap_comp_eq_of_isNilpotent_ker`](thm.html#CerednikDrinfeld.QM.IsFineModuliT.ext_of_comp_forget_eq_of_specMap_comp_eq_of_isNilpotent_ker); unlike the corresponding statement for bare curves, the isomorphism $e$ is given in advance and is the one along which the two extra levels correspond.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_extraLevel_isoTVia_of_isoVia.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuliT

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_extraLevel_isoTVia_of_isoVia
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ} {S : Type} [CommRing S]
    (u u' : FakeEllipticCurve.WithFullLevel Λ N m S) (e : u.1.A ≅ u'.1.A) (he : e.hom ≫ u'.1.f = u.1.f)
    (hiso : FakeEllipticCurve.WithFullLevel.IsoVia u u' e he) (ℓ : ℕ) (C' : u'.1.ExtraLevel ℓ) :
    ∃ C : u.1.ExtraLevel ℓ, FakeEllipticCurve.WithFullLevel.IsoTVia u u' C C' e he := by sorry
