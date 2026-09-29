-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isLevelIsogeny_of_iso_of_isOrder
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_isLevelIsogeny_of_iso_of_isOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/0540507b-360a-5397-bcf8-a4dd790824ff
-- title:
--   Level-ℓ isogeny quotients of isomorphic pairs are isomorphic
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$ that is nonzero, and an algebraically closed field $k$ of characteristic zero; fix a natural number $\ell$ with $\ell>0$ and assume [`QuaternionAlgebra.IsOrder Λ`](def/QuaternionAlgebra_Order.html#L11), i.e. $1\in\Lambda$, $\Lambda$ is closed under multiplication, $\Lambda$ spans $\mathbb{H}[\mathbb{Q},a,b]$ over $\mathbb{Q}$, and $\Lambda$ is finitely generated. Let $u,u'$ be objects of `FakeEllipticCurve.WithExtraLevel Λ N ℓ k`, that is, pairs consisting of a fake elliptic curve over $k$ (a relative group scheme with commutative law, the abelian-scheme property bundle, fibres of dimension $2$, an additive $\Lambda$-action satisfying the trace condition, and a level structure `lev`) together with an extra level at $\ell$: a closed immersion `levK` whose $T$-points form a $\Lambda$-stable subgroup killed by $\ell$, disjoint from `lev`, finite flat of finite presentation of rank $\ell^2$ and geometrically isomorphic to $\mathbb{Z}/\ell\times\mathbb{Z}/\ell$. Let $d,d'$ be fake elliptic curves of level $N$ over $k$. Assume $u\cong u'$ in the sense of `FakeEllipticCurve.WithExtraLevel.Iso` (an isomorphism of the underlying schemes over $k$ respecting the group laws, the $\Lambda$-actions and the factorisation of points through both `lev` and `levK`), and assume `IsLevelIsogeny ℓ u d` and `IsLevelIsogeny ℓ u' d'`: maps $\varphi$ to the target and $\psi$ back, over $k$, additive and $\Lambda$-equivariant, with $\varphi\psi$ and $\psi\varphi$ the action of $\ell$ whenever $\ell\in\Lambda$, with kernel on $T$-points exactly the points factoring through `levK`, and with $\varphi$ carrying `lev`-points to `lev`-points. Then $d$ and $d'$ are isomorphic as fake elliptic curves of level $N$ over $k$: there is an isomorphism of schemes over $k$ compatible with the group laws, the $\Lambda$-actions, and the two level structures.
--
--   This is the well-definedness of the quotient of a fake elliptic curve by an extra level-$\ell$ subgroup: the target of a level-$\ell$ isogeny depends, up to isomorphism of fake elliptic curves with level-$N$ structure, only on the isomorphism class of the pair (curve, extra level). It is used in the construction of the degeneracy maps between the quaternionic moduli towers, in particular by the statements about places and ranks along the tower.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isLevelIsogeny_of_iso_of_isOrder.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_isLevelIsogeny_of_iso_of_isOrder
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} [NeZero N] {k : Type} [Field k] [IsAlgClosed k] [CharZero k] (ℓ : ℕ)
    (hℓ : 0 < ℓ) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ k) (d d' : FakeEllipticCurve Λ N k)
    (huu' : FakeEllipticCurve.WithExtraLevel.Iso u u')
    (hd : FakeEllipticCurve.IsLevelIsogeny ℓ u d) (hd' : FakeEllipticCurve.IsLevelIsogeny ℓ u' d') :
    FakeEllipticCurve.Iso d d' := by sorry
