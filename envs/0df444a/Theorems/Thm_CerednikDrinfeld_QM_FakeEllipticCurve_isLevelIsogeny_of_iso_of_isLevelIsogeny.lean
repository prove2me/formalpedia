-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isLevelIsogeny_of_iso_of_isLevelIsogeny
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.isLevelIsogeny_of_iso_of_isLevelIsogeny
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/f8d626ba-f2b0-5b27-9a75-bacf1b1fc87e
-- title:
--   Level isogeny relation is invariant under isomorphism of the source pair
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, a commutative ring $S$ (in `Type`), and a natural number $\ell$. Let $u=(E,K)$ and $u'=(E',K')$ be elements of `FakeEllipticCurve.WithExtraLevel Λ N ℓ S`, i.e. pairs consisting of a `FakeEllipticCurve Λ N S` together with an `ExtraLevel ℓ` structure on it, and let $d$ be a `FakeEllipticCurve Λ N S`. Assume `WithExtraLevel.Iso u u'`: there is an isomorphism of schemes $e : E.A \cong E'.A$ whose forward map composed with $E'.f$ is $E.f$, which is additive on $T$-valued points for the two relative group laws, which intertwines the $\Lambda$-actions ($E.act\,x$ followed by $e$ equals $e$ followed by $E'.act\,x$ for all $x \in \Lambda$), and under which a $T$-valued point of $E$ factors through $E.lev$ (resp. through $K$'s closed immersion `levK`) if and only if its image factors through $E'.lev$ (resp. through $K'$'s `levK`). Assume also `IsLevelIsogeny ℓ u' d`. The conclusion is `IsLevelIsogeny ℓ u d`: there exist morphisms $\varphi : E.A \to d.A$ over $\operatorname{Spec} S$ and $\psi : d.A \to E.A$ over $\operatorname{Spec} S$, both additive on $T$-valued points, both commuting with the $\Lambda$-actions, such that whenever $(\ell : \mathbb{Q}) \in \Lambda$ one has $\varphi$ followed by $\psi$ equal to $E.act\,\ell$ and $\psi$ followed by $\varphi$ equal to $d.act\,\ell$, such that a $T$-valued point of $E$ is killed by $\varphi$ exactly when it factors through $K$'s `levK`, and such that $\varphi$ sends points factoring through $E.lev$ to points factoring through $d.lev$.
--
--   This is the transport-of-structure statement for the relation 'the fake elliptic curve $d$ is the quotient of the pair $(E,K)$ by its extra level at $\ell$': the relation depends on the pair $u$ only through its isomorphism class. It is used where degeneracy maps between quaternionic moduli data are produced or compared for chosen representatives, and is cited in the construction of degeneracy quotients from coarse moduli data and in the exhaustive decomposition of correspondences on moduli towers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isLevelIsogeny_of_iso_of_isLevelIsogeny.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isLevelIsogeny_of_iso_of_isLevelIsogeny
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] (ℓ : ℕ)
    (u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (d : FakeEllipticCurve Λ N S)
    (huu' : FakeEllipticCurve.WithExtraLevel.Iso u u') (hd : FakeEllipticCurve.IsLevelIsogeny ℓ u' d) :
    FakeEllipticCurve.IsLevelIsogeny ℓ u d := by sorry
