-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isLevelIsogeny_of_isUnit
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isLevelIsogeny_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/1440e865-cda6-5e0c-acc7-6ca587272a10
-- title:
--   Existence of the ℓ-isogeny quotient by an extra level
-- statement:
--   Fix rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order, i.e. $\Lambda$ contains $1$, is closed under multiplication, spans the algebra over $\mathbb{Q}$ and is finitely generated, and is maximal among submodules with these properties. Fix natural numbers $N \neq 0$ and a prime $\ell$, and a commutative ring $S$ (in the bottom universe) in which the image of $\ell$ is a unit. Let $u = (E,K)$ be a fake elliptic curve over $S$ of level $N$ for $\Lambda$ together with an extra level of order $\ell$: thus $E$ consists of a scheme $E.A$ over $\operatorname{Spec} S$ carrying a commutative relative group law, smooth and proper with connected fibres of topological Krull dimension $2$, an action of $\Lambda$ by $S$-endomorphisms that is additive and multiplicative and satisfies the Drinfeld trace condition on tangent spaces at geometric points, and a level-$N$ subgroup scheme $E.\mathrm{lev} : E.C \to E.A$; and $K$ consists of a closed immersion $\mathrm{levK} : K \to E.A$ whose $T$-points form a $\Lambda$-stable subgroup killed by $\ell$, meeting the level-$N$ structure only in the identity, with $\mathrm{levK}$ finite, flat and locally of finite presentation over $S$ of rank $\ell^2$ in every fibre, and isomorphic as a group to $(\mathbb{Z}/\ell)^2$ on geometric points where $\ell \neq 0$. The conclusion is that there exists a fake elliptic curve $d$ over $S$ of level $N$ for $\Lambda$ with $\mathrm{IsLevelIsogeny}\ \ell\ u\ d$: morphisms $\varphi : E.A \to d.A$ and $\psi : d.A \to E.A$ over $\operatorname{Spec} S$, each additive on $T$-points and commuting with the $\Lambda$-actions, such that whenever the image of $\ell$ lies in $\Lambda$ one has $\psi \circ \varphi = E.\mathrm{act}\,\ell$ and $\varphi \circ \psi = d.\mathrm{act}\,\ell$, such that a $T$-point $P$ of $E$ satisfies $\varphi \circ P =$ the identity section of $d$ exactly when $P$ factors through $\mathrm{levK}$, and such that $\varphi$ carries points factoring through $E.\mathrm{lev}$ to points factoring through $d.\mathrm{lev}$.
--
--   This is the quotient construction $d \cong (E/K,\ (C+K)/K)$ for fake elliptic curves with an extra level of order $\ell$ over a base in which $\ell$ is invertible; it is the existence statement underlying the degeneracy map $d_1$ from the moduli of pairs to the moduli of fake elliptic curves. It is used in the construction of the degeneracy quotient and the finiteness of the degeneracy morphism on coarse moduli, and in the pointwise characterisation of the subgroup $K$ by the vanishing of $\varphi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isLevelIsogeny_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isLevelIsogeny_of_isUnit
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsMaximalOrder Λ) (N ℓ : ℕ) [NeZero N] (hℓ : ℓ.Prime)
    {S : Type} [CommRing S] (hℓS : IsUnit ((ℓ : ℕ) : S)) (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) :
    ∃ d : FakeEllipticCurve Λ N S, FakeEllipticCurve.IsLevelIsogeny ℓ u d := by sorry
