-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_id_of_iso_comp_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_id_of_iso_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/b7a543a0-0c4f-573d-a909-84d44ae541f6
-- title:
--   Rigidifying an isomorphism of first-order deformations of a fake elliptic curve
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, an algebraically closed field $k$ of characteristic $\ell$ for a prime $\ell$, a fake elliptic curve $u$ for $\Lambda$ of level $1$ over $k$, and two fake elliptic curves $t,w$ for $\Lambda$ of level $1$ over the dual numbers $\mathrm{DualNumber}\,k = k[\varepsilon]$. Let $g_t : u.A \to t.A$ and $g_w : u.A \to w.A$ be morphisms of schemes each exhibiting $u$ as the pullback of $t$, resp. of $w$, along the projection $\mathrm{fstHom} : k[\varepsilon] \to k$, in the sense of `IsPullbackVia`: the square formed by $g_t$, $u.f$, $t.f$ and $\mathrm{Spec}$ of that projection is cartesian; for every test scheme $T$ with map $t' : T \to \operatorname{Spec} k$ and all $T$-points $P,Q$ of $u.f$ over $t'$, composing the $u$-product of $P,Q$ with $g_t$ gives the $t$-product of $P \circ g_t$ and $Q \circ g_t$ as points over $t'$ followed by $\mathrm{Spec}$ of the projection; $u.\mathrm{act}\,x$ followed by $g_t$ equals $g_t$ followed by $t.\mathrm{act}\,x$ for every $x \in \Lambda$; and every point of $u.f$ factoring through $u.\mathrm{lev}$ has its composite with $g_t$ factoring through $t.\mathrm{lev}$; likewise for $g_w$ and $w$. Assume further an isomorphism of schemes $e : t.A \cong w.A$ with $e.\mathrm{hom}$ followed by $w.f$ equal to $t.f$, and with $g_t$ followed by $e.\mathrm{hom}$ equal to $g_w$. Then there is a morphism $h : t.A \to w.A$ satisfying `IsPullbackVia` for the identity ring homomorphism of $k[\varepsilon]$ — so the square formed by $h$, $t.f$, $w.f$ and $\mathrm{Spec}$ of the identity is cartesian, $h$ takes products of points for $t$'s relative group law to products for $w$'s, $t.\mathrm{act}\,x$ followed by $h$ equals $h$ followed by $w.\mathrm{act}\,x$ for all $x \in \Lambda$, and points factoring through $t.\mathrm{lev}$ are carried to points factoring through $w.\mathrm{lev}$ — and such that $g_t$ followed by $h$ equals $g_w$. The morphism $h$ produced need not be $e.\mathrm{hom}$.
--
--   This is the rigidity step which upgrades an isomorphism of the underlying bare first-order deformations of a level-$1$ fake elliptic curve over an algebraically closed field of characteristic $\ell$ to an isomorphism compatible with the group laws, the $\Lambda$-action and the level structure, and still matching the two comparison maps to the special fibre. It is used in the computation of the tangent space to the deformation problem, by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_fstHom_forall_existsUnique_smul_of_level_one_of_isAlgClosed_of_charP`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_fstHom_forall_existsUnique_smul_of_level_one_of_isAlgClosed_of_charP).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_id_of_iso_comp_eq.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_id_of_iso_comp_eq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (k : Type) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (u : FakeEllipticCurve Λ 1 k)
    (t w : FakeEllipticCurve Λ 1 (DualNumber k)) (gt : u.A ⟶ t.A) (gw : u.A ⟶ w.A)
    (hgt : FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom t u gt)
    (hgw : FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom w u gw)
    (e : t.A ≅ w.A) (he : e.hom ≫ w.f = t.f) (heg : gt ≫ e.hom = gw) :
    ∃ h : t.A ⟶ w.A, FakeEllipticCurve.IsPullbackVia (RingHom.id (DualNumber k)) w t h ∧ gt ≫ h = gw := by sorry
