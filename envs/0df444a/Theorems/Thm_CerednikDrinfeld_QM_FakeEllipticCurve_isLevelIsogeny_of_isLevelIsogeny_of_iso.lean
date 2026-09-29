-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isLevelIsogeny_of_isLevelIsogeny_of_iso
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isLevelIsogeny_of_isLevelIsogeny_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/81ce7c17-2c1a-5bc0-af18-43f920a90431
-- title:
--   Level-ℓ isogenies are stable under isomorphism of the target
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a commutative ring $S$ and a natural number $\ell$. Let $u=(E,K)$ be a fake elliptic curve of level $N$ over $S$ with $\Lambda$-action together with an extra level structure at $\ell$ (a closed subscheme $K\to E.A$ whose $T$-points form a $\Lambda$-stable $\ell$-torsion subgroup, disjoint from the level structure $E.\mathrm{lev}$, finite flat of rank $\ell^2$ with geometric fibres isomorphic to $\mathbb{Z}/\ell\times\mathbb{Z}/\ell$), and let $d$, $D$ be fake elliptic curves of the same type over $S$. Assume `IsLevelIsogeny ℓ u d`: there are morphisms $\varphi : E.A \to d.A$ and $\psi : d.A \to E.A$ over $\mathrm{Spec}\,S$, additive on $T$-points for the relative group laws, commuting with the $\Lambda$-actions, with $\varphi$ followed by $\psi$ equal to the action of $\ell$ on $E.A$ and $\psi$ followed by $\varphi$ equal to the action of $\ell$ on $d.A$ whenever $\ell \in \Lambda$, whose kernel on $T$-points is exactly the set of points factoring through $K$, and which carries points factoring through $E.\mathrm{lev}$ to points factoring through $d.\mathrm{lev}$. Assume also `Iso d D`: an isomorphism of schemes $e : d.A \cong D.A$ over $\mathrm{Spec}\,S$, additive on $T$-points, commuting with the $\Lambda$-actions, and matching the two level structures on $T$-points. Then `IsLevelIsogeny ℓ u D` holds.
--
--   This is the transport of a level-$\ell$ isogeny along an isomorphism of its target, the well-definedness statement needed to treat level-$\ell$ isogenies as data on isomorphism classes of fake elliptic curves with extra level structure. It is used in the proof that the degeneracy map between the coarse moduli objects is finite.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isLevelIsogeny_of_isLevelIsogeny_of_iso.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isLevelIsogeny_of_isLevelIsogeny_of_iso
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] (ℓ : ℕ)
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (d D : FakeEllipticCurve Λ N S)
    (hd : FakeEllipticCurve.IsLevelIsogeny ℓ u d) (h : FakeEllipticCurve.Iso d D) :
    FakeEllipticCurve.IsLevelIsogeny ℓ u D := by sorry
