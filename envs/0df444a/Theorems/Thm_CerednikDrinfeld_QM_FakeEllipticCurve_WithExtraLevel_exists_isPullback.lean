-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/1861a03c-a5bc-5df6-acb9-3aa7ac03855c
-- title:
--   Base change of a fake elliptic curve with extra level
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, natural numbers $N,\ell$, commutative rings $S,S'$ (of type `Type`, so all schemes live in universe $0$) and a ring homomorphism $\varphi : S \to S'$. Let $u$ be a pair over $S$: a fake elliptic curve $E$ of level $N$ with $\Lambda$-action — a scheme $A$ with structure morphism $f : A \to \operatorname{Spec} S$, a commutative relative group law on the functor of points of $f$, the property bundle of an abelian scheme (smooth, proper, connected fibres, a group law existing), all fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms over $S$ which is additive and multiplicative and satisfies the trace condition on tangent spaces at geometric points, and a level structure $\mathrm{lev} : C \to A$ — together with an extra level-$\ell$ structure, i.e. a closed immersion $\mathrm{levK} : K \to A$ whose points form a $\Lambda$-stable subgroup killed by $\ell$, meeting the level structure only in the identity, finite flat of finite presentation of rank $\ell^2$ over $S$, with geometric fibres isomorphic as groups to $(\mathbb{Z}/\ell)^2$ whenever $\ell$ is invertible. The conclusion asserts the existence of such a pair $u'$ over $S'$ with `WithExtraLevel.IsPullback` $\varphi\, u\, u'$: there are a morphism $g : A' \to A$ making the square formed by $g$, $f'$, $f$ and $\operatorname{Spec}\varphi$ a pullback square, such that $g$ transports the group law (for every scheme $T$, every $t' : T \to \operatorname{Spec} S'$ and all points $P,Q$ of $f'$ over $t'$, the product $P\cdot Q$ followed by $g$ is the product of $P$ followed by $g$ and $Q$ followed by $g$, taken over $t'$ followed by $\operatorname{Spec}\varphi$), such that $\mathrm{act}'(x)$ followed by $g$ equals $g$ followed by $\mathrm{act}(x)$ for every $x \in \Lambda$, and such that for every point $P$ of $f'$ over $t'$: if $P$ factors through $\mathrm{lev}'$ then $P$ followed by $g$ factors through $\mathrm{lev}$, and if $P$ factors through $\mathrm{levK}'$ then $P$ followed by $g$ factors through $\mathrm{levK}$. Note that the two level clauses are required only in this one direction.
--
--   This is the existence of the base change along $\varphi : S \to S'$ of a fake elliptic curve with $\Lambda$-action, level-$N$ structure and extra level-$\ell$ structure, the functoriality needed for the moduli problem of the Čerednik–Drinfeld description to be a functor on commutative rings. It is used in the construction of auxiliary full-level covers and in the comparison of level structures after base change to algebraically closed fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) :
    ∃ u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S', FakeEllipticCurve.WithExtraLevel.IsPullback φ u u' := by sorry
