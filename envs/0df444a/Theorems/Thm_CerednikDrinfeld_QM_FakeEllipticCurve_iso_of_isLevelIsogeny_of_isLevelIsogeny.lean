-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isLevelIsogeny_of_isLevelIsogeny
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_isLevelIsogeny_of_isLevelIsogeny
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/e0f47722-88fd-57c7-a91e-09421ebb2ea0
-- title:
--   Uniqueness of the level-ℓ isogeny quotient over a general base
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ which is an order in the sense of the project's `IsOrder`: $1 \in \Lambda$, $\Lambda$ is closed under multiplication, its $\mathbb{Q}$-span is everything, and it is finitely generated. Let $N$ be a nonzero natural number, $\ell$ a natural number with $0 < \ell$, and $S$ a commutative ring. Let $u = (E,K)$ consist of a fake elliptic curve $E$ over $S$ with $\Lambda$-action and level-$N$ datum `lev` (a `FakeEllipticCurve Λ N S`) together with an extra level structure $K$ at $\ell$: a closed subscheme of $E$, finite flat of finite presentation over $S$ of rank $\ell^2$ in each fibre, stable under the group law and under $\Lambda$, killed by $\ell$, geometrically isomorphic to $(\mathbb{Z}/\ell)^2$ at fibres where $\ell$ is invertible, and meeting `lev` trivially. Let $d$ and $d_1$ be fake elliptic curves over $S$ of the same type, each a level-$\ell$ isogeny quotient of $u$: there are mutually quasi-inverse morphisms over $S$ between $E$ and the target, additive on $T$-points and $\Lambda$-equivariant, whose composites in either order equal the action of $\ell$ when $\ell \in \Lambda$, with kernel on $T$-points exactly the points factoring through $K$, and carrying `lev`-points to `lev`-points. The conclusion is `FakeEllipticCurve.Iso d d₁`: an isomorphism of schemes $d \to d_1$ over $S$, additive on $T$-points, commuting with the $\Lambda$-actions, and matching the level-$N$ data in the sense that a $T$-point factors through the one `lev` exactly when its image factors through the other.
--
--   This is the uniqueness statement for the quotient $E/K$ of a fake elliptic curve by an extra level structure at $\ell$, formulated over an arbitrary commutative base ring rather than over an algebraically closed field. It makes the assignment $u \mapsto E/K$ well defined up to isomorphism, and is used in the construction of the degeneracy morphisms on coarse moduli schemes and in the analysis of uniformised Hecke curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isLevelIsogeny_of_isLevelIsogeny.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_isLevelIsogeny_of_isLevelIsogeny
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ) {N : ℕ} [NeZero N]
    (ℓ : ℕ) (hℓ : 0 < ℓ) (S : Type) [CommRing S]
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (d d₁ : FakeEllipticCurve Λ N S)
    (h : FakeEllipticCurve.IsLevelIsogeny ℓ u d) (h₁ : FakeEllipticCurve.IsLevelIsogeny ℓ u d₁) :
    FakeEllipticCurve.Iso d d₁ := by sorry
