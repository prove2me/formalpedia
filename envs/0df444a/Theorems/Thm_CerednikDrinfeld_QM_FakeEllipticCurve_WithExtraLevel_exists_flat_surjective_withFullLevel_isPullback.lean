-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_flat_surjective_withFullLevel_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_flat_surjective_withFullLevel_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/687108ab-fc29-5d50-9df4-e2c080fc39c7
-- title:
--   Flat-local existence of full level structures, with extra level
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $q,q'$ be primes such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite and ramified exactly at $q,q'$, in the sense that $0<a$ or $0<b$ and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit precisely when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order and is maximal among orders, let $N,m,\ell$ be natural numbers, let $S$ be a commutative ring in which $m$ is invertible, and let $u=(E,K)$ consist of a fake elliptic curve $E$ over $S$ of level $N$ — a scheme $A$ over $\operatorname{Spec} S$ with a commutative relative group law, the abelian-scheme property bundle, two-dimensional fibres, a $\Lambda$-action by group endomorphisms over $S$ satisfying the trace condition, and the level-$N$ datum $\mathrm{lev}$ — together with an extra level structure $K$ at $\ell$ on $E$: a closed immersion $\mathrm{levK}:K\to A$ whose points form a $\Lambda$-stable subgroup killed by $\ell$, disjoint from $\mathrm{lev}$, finite flat of finite presentation of rank $\ell^2$ with geometric fibres isomorphic to $(\mathbb{Z}/\ell)^2$. Then there exist a commutative ring $S'$ and a ring homomorphism $\varphi:S\to S'$ such that $\operatorname{Spec}\varphi$ is flat and surjective, a fake elliptic curve over $S'$ of level $N$ equipped with a full level-$m$ structure, and an extra level structure $K'$ at $\ell$ on that curve, such that the resulting pair over $S'$ is a pullback of $(E,K)$ along $\varphi$: there is a morphism $g$ from the curve over $S'$ to $A$ making the square with the two structure morphisms and $\operatorname{Spec}\varphi$ a pullback square, compatible with the group laws on $T$-points, commuting with the $\Lambda$-actions, and carrying points factoring through the level-$N$, respectively extra level, data over $S'$ to points factoring through $\mathrm{lev}$, respectively $\mathrm{levK}$. No compatibility is imposed on the full level-$m$ structure itself.
--
--   This is the rigidification step which makes a pair consisting of a fake elliptic curve and an extra level structure acquire a full level-$m$ structure after a faithfully flat base change, the flat-local existence statement underlying the passage from the fine to the coarse moduli problem for quaternionic Shimura curves. It is used in the construction of a coarse moduli space as a quotient of a fine one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_flat_surjective_withFullLevel_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_flat_surjective_withFullLevel_isPullback
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} (m ℓ : ℕ)
    (S : Type) [CommRing S] (hm : IsUnit ((m : ℕ) : S)) (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) :
    ∃ (S' : Type) (_ : CommRing S') (φ : S →+* S'),
      Flat (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) ∧
      ∃ (w' : FakeEllipticCurve.WithFullLevel Λ N m S') (K' : w'.1.ExtraLevel ℓ),
        FakeEllipticCurve.WithExtraLevel.IsPullback φ u ⟨w'.1, K'⟩ := by sorry
