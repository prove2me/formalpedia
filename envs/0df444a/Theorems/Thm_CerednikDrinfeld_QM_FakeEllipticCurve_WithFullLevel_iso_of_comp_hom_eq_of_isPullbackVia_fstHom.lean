-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_iso_of_comp_hom_eq_of_isPullbackVia_fstHom
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.iso_of_comp_hom_eq_of_isPullbackVia_fstHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/a3479629-d5ca-58f1-9701-8167c4701631
-- title:
--   Rigidity for first-order deformations with full level structure
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, and naturals $N,m$. Let $k$ be a field in which $N$ and $m$ are units, let $u$ be a fake elliptic curve over $k$ with level-$N$ datum and a full level-$m$ structure (a pair consisting of an object of `FakeEllipticCurve Λ N k` and a `FullLevel m` structure on it), and let $w,t$ be two such objects over the dual numbers $k[\varepsilon]$. Assume given $gw : u.1.A \to w.1.A$ with `IsPullbackVia` for $\varepsilon \mapsto 0$, that is: the square formed by $gw$, the structure maps of $u$ and $w$ and $\operatorname{Spec}$ of $\varepsilon \mapsto 0$ is a pullback, $gw$ carries the relative group law of $u$ on points to that of $w$, intertwines the $\Lambda$-actions ($u.1.\mathrm{act}\,x$ followed by $gw$ equals $gw$ followed by $w.1.\mathrm{act}\,x$), and sends points factoring through the level subscheme $u.1.\mathrm{lev}$ to points factoring through $w.1.\mathrm{lev}$; assume also $hgwP$, that the full-level point of $u$ composed with $gw$ equals $\operatorname{Spec}$ of $\varepsilon\mapsto 0$ followed by the full-level point of $w$. Assume the same data $gt$ for $t$. Finally let $e : w.1.A \cong t.1.A$ be an isomorphism of schemes over $\operatorname{Spec} k[\varepsilon]$ (i.e. $e.\mathrm{hom}$ followed by $t.1.f$ is $w.1.f$) with $gw$ followed by $e.\mathrm{hom}$ equal to $gt$. The conclusion is `WithFullLevel.Iso w t`: there exists an isomorphism $w.1.A \cong t.1.A$ over $\operatorname{Spec} k[\varepsilon]$ which is a homomorphism for the relative group laws on points over every base, commutes with the $\Lambda$-actions, matches factorisation through the level subschemes in both directions, and carries the full-level point of $w$ to that of $t$. (Existence of such an isomorphism is asserted; it is not claimed that $e$ itself has these properties.)
--
--   This is the rigidity step for first-order deformations in the fine moduli theory of fake elliptic curves: an abstract isomorphism of the total spaces of two deformations of the same special fibre, compatible with the comparison maps to that fibre, already yields an isomorphism of the deformations as objects with $\Lambda$-action, level-$N$ datum and full level-$m$ structure. It is used in the construction of the unique first-order deformation parameters underlying the Čerednik–Drinfeld comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_iso_of_comp_hom_eq_of_isPullbackVia_fstHom.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.iso_of_comp_hom_eq_of_isPullbackVia_fstHom
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ}
    (k : Type) [Field k] (hN : IsUnit ((N : ℕ) : k)) (hm' : IsUnit ((m : ℕ) : k))
    (u : FakeEllipticCurve.WithFullLevel Λ N m k)
    (w t : FakeEllipticCurve.WithFullLevel Λ N m (DualNumber k))
    (gw : u.1.A ⟶ w.1.A) (hgw : FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom w.1 u.1 gw)
    (hgwP : (u.2.P).1 ≫ gw = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ (w.2.P).1)
    (gt : u.1.A ⟶ t.1.A) (hgt : FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom t.1 u.1 gt)
    (hgtP : (u.2.P).1 ≫ gt = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ (t.2.P).1)
    (e : w.1.A ≅ t.1.A) (he : e.hom ≫ t.1.f = w.1.f) (hge : gw ≫ e.hom = gt) :
    FakeEllipticCurve.WithFullLevel.Iso w t := by sorry
