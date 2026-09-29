-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_isAtkinLehnerQuotient_of_iso_of_iso
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.isAtkinLehnerQuotient_of_iso_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/cd3388fd-299b-5bef-82f5-bca6af52acc3
-- title:
--   Atkin–Lehner quotient relation is invariant under isomorphism of pairs
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$, natural numbers $N$, $\ell$, $r$ and a commutative ring $S$, and let $u,u',v,v'$ be objects of `QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ S`, i.e. pairs consisting of a fake elliptic curve over $S$ with $\Lambda$-action and level-$N$ datum together with an extra level structure at $\ell$ on it. Assume `IsAtkinLehnerQuotient r u u'`: there are mutually inverse-up-to-$[r]$ morphisms $\varphi : A_u \to A_{u'}$ and $\psi : A_{u'} \to A_u$ over $S$, each additive on $T$-points for the relative group laws, each commuting with the $\Lambda$-actions, satisfying $\varphi$ followed by $\psi$ equal to the action of $r$ on $u$ and $\psi$ followed by $\varphi$ equal to the action of $r$ on $u'$ whenever $r \in \Lambda$, with the kernel of $\varphi$ on $T$-points described by vanishing under all $m \in \Lambda$ with $m\,\bar m = rn$, and with $\varphi$ carrying points factoring through the level structure of $u$, respectively through the extra level of $u$, into the corresponding ones for $u'$. Assume further `Iso u v` and `Iso u' v'`, i.e. isomorphisms of the underlying schemes over $S$ that are additive on points, $\Lambda$-equivariant, and match the level and extra-level subschemes in the sense that factoring through them corresponds on both sides. Then `IsAtkinLehnerQuotient r v v'` holds.
--
--   This is the invariance of the Atkin–Lehner quotient relation under isomorphism in the moduli problem of fake elliptic curves with an extra level structure at $\ell$, transporting the quotient datum along the two isomorphisms. It is used in the construction of the moduli tower with Atkin–Lehner involutions in the Čerednik–Drinfeld part of the argument, notably by the companion statement deducing an isomorphism from two Atkin–Lehner quotient relations and by the tower-law results.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_isAtkinLehnerQuotient_of_iso_of_iso.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld QuaternionAlgebra

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.isAtkinLehnerQuotient_of_iso_of_iso
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} {S : Type u} [CommRing S] (r : ℕ)
    (u u' v v' : QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ S)
    (h : QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r u u')
    (hu : QM.FakeEllipticCurve.WithExtraLevel.Iso u v) (hu' : QM.FakeEllipticCurve.WithExtraLevel.Iso u' v') :
    QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r v v' := by sorry
