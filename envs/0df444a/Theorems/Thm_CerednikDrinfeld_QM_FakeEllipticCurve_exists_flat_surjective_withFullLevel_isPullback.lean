-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_flat_surjective_withFullLevel_isPullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_flat_surjective_withFullLevel_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/ce2f5ff7-55f8-5f2d-b274-ae0ddf9de9ec
-- title:
--   Full level-m structures exist flat-locally on the base
-- statement:
--   Fix $a,b\in\mathbb{Q}$ and primes $q,q'$, and assume `IsIndefiniteRamifiedExactlyAt a b q q'`: that $0<a$ or $0<b$, and that for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ that is an order and is maximal among orders for inclusion, let $N,m\in\mathbb{N}$, let $S$ be a commutative ring in which the image of $m$ is a unit, and let $E$ be a fake elliptic curve over $S$ of level $N$ with $\Lambda$-action (a scheme $A$ over $\operatorname{Spec} S$ with commutative relative group law, abelian-scheme property bundle, all fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms over $S$ additive and multiplicative in $\Lambda$ with the prescribed trace identity, and the level data). Then there are a commutative ring $S'$ and a ring homomorphism $\varphi:S\to S'$ with $\operatorname{Spec}\varphi$ flat and surjective, a fake elliptic curve $E'$ over $S'$ carrying a full level-$m$ structure — an $S'$-point $P$ of $E'$ with $mP=0$ whose $\Lambda$-translates at every geometric point of $S'$ exhaust the $m$-torsion, and whose annihilator in $\Lambda$ at every geometric point is exactly $m\Lambda$ — such that `FakeEllipticCurve.IsPullback φ E E'` holds: some $g:E'.A\to E.A$ makes the square over $\operatorname{Spec}\varphi$ cartesian, is compatible with the group laws and with the $\Lambda$-actions, and carries points factoring through $E'$'s level map to points factoring through $E$'s. The pullback condition constrains only the underlying curves, not $P$.
--
--   This is the descent step making the moduli problem of fake elliptic curves with full level-$m$ structure (for $m$ invertible on the base) representable after a faithfully flat base change, the level structure being produced at geometric points and then spread out over the finite étale $m$-torsion scheme. It feeds the comparison between the coarse and fine moduli descriptions of Shimura curves attached to a maximal order in an indefinite quaternion algebra ramified exactly at $q$ and $q'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_flat_surjective_withFullLevel_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_flat_surjective_withFullLevel_isPullback
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} (m : ℕ)
    (S : Type) [CommRing S] (hm : IsUnit ((m : ℕ) : S)) (E : FakeEllipticCurve Λ N S) :
    ∃ (S' : Type) (_ : CommRing S') (φ : S →+* S'),
      Flat (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) ∧
      ∃ u' : FakeEllipticCurve.WithFullLevel Λ N m S', FakeEllipticCurve.IsPullback φ E u'.1 := by sorry
