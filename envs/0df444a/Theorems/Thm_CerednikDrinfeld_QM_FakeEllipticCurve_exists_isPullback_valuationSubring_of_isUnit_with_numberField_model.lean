-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_valuationSubring_of_isUnit_with_numberField_model
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_valuationSubring_of_isUnit_with_numberField_model
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/c9ed856c-d05b-5595-8ee7-c32baf3ed57c
-- title:
--   Fake elliptic curves over ℚ̄ extend over valuation rings
-- statement:
--   Fix natural numbers $N, q, q'$ with $N \neq 0$, $q$ and $q'$ prime, $q \nmid N$, $q' \nmid N$ and $q' \neq q$, and rationals $a, b$ such that the quaternion algebra $\mathbb H[\mathbb Q, a, b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the completion $\mathbb H[\mathbb Q,a,b] \otimes_{\mathbb Q} \mathbb Q_v$ has every nonzero element a unit precisely when $q \in v$ or $q' \in v$. Let $\Lambda$ be a $\mathbb Z$-submodule of $\mathbb H[\mathbb Q,a,b]$ that is a maximal order, i.e. it contains $1$, is closed under multiplication, is finitely generated, spans the algebra over $\mathbb Q$, and is maximal among submodules with these properties. Then for every valuation subring $B$ of $\mathrm{AlgebraicClosure}\ \mathbb Q$ in which the image of the integer $Nqq'$ is a unit, and every fake elliptic curve $E$ over $\mathrm{AlgebraicClosure}\ \mathbb Q$ of level $N$ with $\Lambda$-action — an object of `FakeEllipticCurve Λ N`, consisting of a scheme over the base carrying a commutative relative group law, smooth and proper with connected fibres, all fibres of topological Krull dimension $2$, together with an action of $\Lambda$ by base-preserving endomorphisms that is additive and multiplicative and whose induced endomorphism of the tangent space at an algebraically closed geometric point has trace equal to the reduced trace $m + \bar m$, and with a scheme $C$ and morphism `lev` encoding the level-$N$ data — there exist a fake elliptic curve $\mathcal A$ over $B$, an intermediate field $K'$ of $\mathbb Q \subseteq \mathrm{AlgebraicClosure}\ \mathbb Q$ of finite degree over $\mathbb Q$, a ring homomorphism $\iota_0$ from $B \cap K'$ to $B$ which is the identity on elements of $\mathrm{AlgebraicClosure}\ \mathbb Q$, and a fake elliptic curve $\mathcal A_0$ over $B \cap K'$, such that $\mathcal A$ pulls back to $E$ along the inclusion $B \hookrightarrow \mathrm{AlgebraicClosure}\ \mathbb Q$, $\mathcal A_0$ pulls back to $\mathcal A$ along $\iota_0$, and $\mathcal A_0$ pulls back to $E$ along $B \cap K' \hookrightarrow \mathrm{AlgebraicClosure}\ \mathbb Q$; here `IsPullback φ` asserts the existence of a morphism of the underlying schemes making the square over $\mathrm{Spec}$ of $\varphi$ cartesian, compatible with the relative group laws on $T$-points, commuting with the action of each element of $\Lambda$, and sending points factoring through the level structure to points factoring through the level structure of the target.
--
--   This is the potentially-good-reduction step for fake elliptic curves: every fake elliptic curve over $\bar{\mathbb Q}$ is, after passing to a number field $K'$, the base change of a model over the valuation ring $B \cap K'$ and hence over $B$ itself, whenever $Nqq'$ is invertible in $B$. It is used in the construction of integral models of the Shimura curve attached to $\Lambda$ and of the associated Hecke tower, and in the analysis of the Frobenius action on their special fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_valuationSubring_of_isUnit_with_numberField_model.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_valuationSubring_of_isUnit_with_numberField_model
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) :
    ∀ (B : ValuationSubring (AlgebraicClosure ℚ)), IsUnit (((N * q * q' : ℕ) : ℤ) : ↥B) →
      ∀ E : CerednikDrinfeld.QM.FakeEllipticCurve Λ N (AlgebraicClosure ℚ),
        ∃ (𝒜 : CerednikDrinfeld.QM.FakeEllipticCurve Λ N ↥B)
          (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ ↥K')
          (ι₀ : ↥(B.toSubring ⊓ K'.toSubring) →+* ↥B)
          (_ : ∀ x : ↥(B.toSubring ⊓ K'.toSubring), (ι₀ x : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))
          (𝒜₀ : CerednikDrinfeld.QM.FakeEllipticCurve Λ N ↥(B.toSubring ⊓ K'.toSubring)),
          CerednikDrinfeld.QM.FakeEllipticCurve.IsPullback (B.subtype : ↥B →+* AlgebraicClosure ℚ) 𝒜 E ∧
          CerednikDrinfeld.QM.FakeEllipticCurve.IsPullback ι₀ 𝒜₀ 𝒜 ∧
          CerednikDrinfeld.QM.FakeEllipticCurve.IsPullback
            ((B.toSubring ⊓ K'.toSubring).subtype : ↥(B.toSubring ⊓ K'.toSubring) →+* AlgebraicClosure ℚ) 𝒜₀ E := by sorry
