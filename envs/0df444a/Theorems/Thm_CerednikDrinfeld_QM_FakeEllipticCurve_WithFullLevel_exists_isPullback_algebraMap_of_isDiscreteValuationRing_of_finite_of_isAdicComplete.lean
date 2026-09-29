-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_algebraMap_of_isDiscreteValuationRing_of_finite_of_isAdicComplete
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_algebraMap_of_isDiscreteValuationRing_of_finite_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/42c8f2d7-e5ed-5211-93b0-cc1328a25176
-- title:
--   Full-level fake elliptic curves extend over complete discrete valuation rings
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, let $N\neq 0$ and let $a,b\in\mathbb Q$ be such that $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the algebra $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ has all nonzero elements invertible exactly when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ be a $\mathbb Z$-submodule which is an order and is maximal among the orders containing it, and let $m\geq 3$. Let $R$ be a discrete valuation domain with finite residue field, complete for the adic topology of its maximal ideal, with $K$ a fraction field of $R$, and assume the images of $N$ and of $m$ in $R$ are units. Then for every object $u$ of `FakeEllipticCurve.WithFullLevel Λ N m K`, that is, a fake elliptic curve over $K$ with $\Lambda$-action and level-$N$ datum together with a full level-$m$ structure, there is such an object $\mathfrak u$ over $R$ and a morphism $g$ from the total space of $u$ to that of $\mathfrak u$ making the total space of $u$ a pullback of that of $\mathfrak u$ along $\mathrm{Spec}$ of $R\to K$, compatible with the relative group laws, with the $\Lambda$-actions, carrying points factoring through the level-$N$ subscheme of $u$ to points factoring through that of $\mathfrak u$, and sending the full level-$m$ section of $u$ to the base change of that of $\mathfrak u$.
--
--   This is the good-reduction, or extension, step for the fine moduli problem of fake elliptic curves with full level-$m$ structure: over a complete discrete valuation ring with finite residue field in which $N$ and $m$ are invertible, a $K$-valued point of the moduli problem lifts to an $R$-valued point. It supplies the existence half of the valuative criterion used in [`CerednikDrinfeld.QM.IsFineModuli.isProper_localizationAway_six_mul`](thm.html#CerednikDrinfeld.QM.IsFineModuli.isProper_localizationAway_six_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_algebraMap_of_isDiscreteValuationRing_of_finite_of_isAdicComplete.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_algebraMap_of_isDiscreteValuationRing_of_finite_of_isAdicComplete
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {m : ℕ} (hm : 3 ≤ m)
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    (hN : IsUnit ((N : ℕ) : R)) (hmu : IsUnit ((m : ℕ) : R))
    (u : FakeEllipticCurve.WithFullLevel Λ N m K) :
    ∃ 𝔲 : FakeEllipticCurve.WithFullLevel Λ N m R,
      FakeEllipticCurve.WithFullLevel.IsPullback (algebraMap R K) 𝔲 u := by sorry
