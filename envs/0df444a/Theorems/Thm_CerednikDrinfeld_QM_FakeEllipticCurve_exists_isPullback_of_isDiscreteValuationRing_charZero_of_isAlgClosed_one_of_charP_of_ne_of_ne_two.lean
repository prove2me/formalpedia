-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_of_isDiscreteValuationRing_charZero_of_isAlgClosed_one_of_charP_of_ne_of_ne_two
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_of_isDiscreteValuationRing_charZero_of_isAlgClosed_one_of_charP_of_ne_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/994995c7-c93a-55cd-9a7f-cab3b25396d7
-- title:
--   Lifting a level-one fake elliptic curve to a complete DVR
-- statement:
--   Let $q \neq q'$ be primes and let $a, b \in \mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q}, a, b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q}, a, b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all its nonzero elements units precisely when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q}, a, b]$ be a $\mathbb{Z}$-submodule which is an order maximal among the orders containing it, let $\mu \in \Lambda$ satisfy $\mu^2 = -(qq') \cdot 1$, and let $\mathrm{star} : \Lambda \to \Lambda$ satisfy $\mu \cdot \mathrm{star}(x) = \bar{x} \cdot \mu$ for all $x \in \Lambda$, where $\bar{\;}$ is quaternionic conjugation. Let $k$ be an algebraically closed field of characteristic $p$ with $p \neq q$, $p \neq q'$ and $p \neq 2$, and let $E$ be a fake elliptic curve over $k$ for $\Lambda$ at level $N = 1$: an abelian scheme datum over $\operatorname{Spec} k$ with commutative relative group law, all fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms over the base compatible with addition and multiplication and with the prescribed trace condition on tangent spaces, together with the level-structure data of `FakeEllipticCurve`. Then there exist a ring $R$ which is a domain and a discrete valuation ring of characteristic zero, and a surjective ring homomorphism $\varphi : R \to k$, such that $R$ is complete for the $\mathfrak{m}_R$-adic topology, and there exists a fake elliptic curve $E_R$ over $R$ for $\Lambda$ at level $1$ with `FakeEllipticCurve.IsPullback` $\varphi\, E_R\, E$: a morphism $g : E.A \to E_R.A$ whose square over $\operatorname{Spec} \varphi$ is a pullback, compatible with the two relative group laws and with the $\Lambda$-actions, and such that points of $E$ factoring through its level subscheme are carried, after composition with $g$, into the level subscheme of $E_R$.
--
--   This is the branch, at a residue characteristic $p$ dividing neither ramified prime of the quaternion algebra and different from $2$, of the lifting statement for fake elliptic curves (QM abelian surfaces) at trivial level: every such surface over an algebraically closed field lifts to a characteristic-zero complete discrete valuation ring with that field as residue field. It feeds the characteristic-zero comparison used in the study of the Čerednik–Drinfeld moduli of fake elliptic curves, and is cited by the corresponding statement with $2$ assumed invertible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_of_isDiscreteValuationRing_charZero_of_isAlgClosed_one_of_charP_of_ne_of_ne_two.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_of_isDiscreteValuationRing_charZero_of_isAlgClosed_one_of_charP_of_ne_of_ne_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpq : p ≠ q) (hpq' : p ≠ q') (hp2 : p ≠ 2)
    (E : FakeEllipticCurve Λ 1 k) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R) (_ : CharZero R) (φ : R →+* k),
      Function.Surjective φ ∧ IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧
      ∃ E_R : FakeEllipticCurve Λ 1 R, FakeEllipticCurve.IsPullback φ E_R E := by sorry
