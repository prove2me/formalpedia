-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_valuationSubring_inf_of_isPullback_algebraMap_of_isUnit
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_valuationSubring_inf_of_isPullback_algebraMap_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/78f02c9e-19f9-50ef-b296-47939c06e13f
-- title:
--   Extension of fake elliptic curves over valuation subrings of ℚ̄
-- statement:
--   Fix natural numbers $N, q, q'$ with $N$ nonzero and $q, q'$ prime, assume $q \nmid N$, $q' \nmid N$ and $q' \neq q$, and fix $a, b \in \mathbb{Q}$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q}, a, b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q}, a, b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all its nonzero elements invertible exactly when $q \in v$ or $q' \in v$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q}, a, b]$ which is a maximal order: it contains $1$, is closed under multiplication, spans the algebra over $\mathbb{Q}$, is finitely generated, and every order containing it equals it. Let $K$ be an intermediate field of $\mathbb{Q} \subseteq \overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with $[K : \mathbb{Q}]$ finite, let $E_0$ be a fake elliptic curve over $K$ and $E$ one over $\overline{\mathbb{Q}}$ — in each case, in the sense of the structure `FakeEllipticCurve`, a scheme $A$ over the base equipped with a commutative relative group law, the abelian-scheme property bundle (smooth, proper, connected fibres, a relative group law existing), fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms over the base which is additive and anti-multiplicative, normalised at $1$ and subject to the trace condition relating $\mathrm{tr}$ of $m$ on the tangent space to the reduced trace $m + \bar m$, together with the level-$N$ data — and assume `FakeEllipticCurve.IsPullback` for the inclusion $K \hookrightarrow \overline{\mathbb{Q}}$, that is, a morphism $g : E.A \to E_0.A$ making a pullback square of $E.f$ against $E_0.f$ over $\mathrm{Spec}$ of that inclusion, compatible with the two group laws, commuting with the $\Lambda$-actions, and sending points factoring through the level structure of $E$ to points factoring through that of $E_0$. Finally let $B$ be a valuation subring of $\overline{\mathbb{Q}}$ in which the image of the integer $N q q'$ is a unit. Then there exist an intermediate field $K'$ of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$, finite over $\mathbb{Q}$ and containing $K$, and a fake elliptic curve $\mathcal{A}$ for $\Lambda$ and level $N$ over the ring $B \cap K'$ (the intersection of the underlying subrings) such that `FakeEllipticCurve.IsPullback` holds for the inclusion $B \cap K' \hookrightarrow \overline{\mathbb{Q}}$, with $\mathcal{A}$ and $E$ in those roles.
--
--   This is the potential-good-reduction step for fake elliptic curves: given a model of $E$ over a number field, it produces an integral model with its $\Lambda$-action and level-$N$ structure over the valuation ring cut out on a finite extension $K'$ by an arbitrary valuation subring of $\overline{\mathbb{Q}}$ in which $Nqq'$ is invertible. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_valuationSubring_of_isUnit_with_numberField_model`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_valuationSubring_of_isUnit_with_numberField_model), which removes the hypothesis of a given number-field model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_valuationSubring_inf_of_isPullback_algebraMap_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open AlgebraicCurve
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_valuationSubring_inf_of_isPullback_algebraMap_of_isUnit
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (E₀ : FakeEllipticCurve Λ N K) (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (hE : FakeEllipticCurve.IsPullback (algebraMap K (AlgebraicClosure ℚ)) E₀ E)
    (B : ValuationSubring (AlgebraicClosure ℚ)) (hu : IsUnit (((N * q * q' : ℕ) : ℤ) : ↥B)) :
    ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K') (_ : K ≤ K')
      (𝒜 : FakeEllipticCurve Λ N ↥(B.toSubring ⊓ K'.toSubring)),
      FakeEllipticCurve.IsPullback (B.toSubring ⊓ K'.toSubring).subtype 𝒜 E := by sorry
