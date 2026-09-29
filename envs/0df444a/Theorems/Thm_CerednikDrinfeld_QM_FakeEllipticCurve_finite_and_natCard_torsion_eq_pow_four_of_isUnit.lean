-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_finite_and_natCard_torsion_eq_pow_four_of_isUnit
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.finite_and_natCard_torsion_eq_pow_four_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/14ffeb09-82bc-55e5-99d2-3860f970a98b
-- title:
--   m-torsion of a fake elliptic curve has m⁴ points
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$, and let $k$ be an algebraically closed field (in the base universe). Let $E$ be a fake elliptic curve of type $(\Lambda,N)$ over $k$: thus $E$ provides a scheme $E.A$ with a structure morphism $E.f : E.A \to \operatorname{Spec} k$, a relative group law $E.L$ on $E.f$ (functorial multiplication, unit and inverse on sections over arbitrary bases, associative, unital, with inverses, and compatible with base change), commutativity of $E.L$, the abelian-scheme property bundle for $E.f$ (smooth, proper, connected fibres, a relative group law exists), all fibres of $E.f$ of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms of $E.A$ over the base which is multiplicative in $\Lambda$, additive on sections and satisfies the trace condition $\operatorname{tr}(\Phi_m) = n$ whenever $m + \bar m = n$, together with the remaining fields of the structure, summarised here. Let $m$ be a natural number whose image in $k$ is a unit. Then the set of sections $P$ of $E.f$ over the identity of $\operatorname{Spec} k$ (morphisms $\operatorname{Spec} k \to E.A$ composing with $E.f$ to the identity) with $m$-fold sum $P + \dots + P$, formed by iterating $E.L$'s multiplication starting from its unit, equal to the unit section, is finite, and its cardinality is $m^4$.
--
--   This is the classical count of $m$-torsion points on an abelian surface over an algebraically closed field of characteristic not dividing $m$, specialised to fake elliptic curves, where the group $E[m](k)$ is to be compared with $\Lambda/m\Lambda$. It is used in the construction and comparison of full level-$m$ structures on fake elliptic curves, where two finite sets of the same cardinality $m^4$ are identified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_finite_and_natCard_torsion_eq_pow_four_of_isUnit.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.finite_and_natCard_torsion_eq_pow_four_of_isUnit
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (k : Type) [Field k] [IsAlgClosed k]
    (E : FakeEllipticCurve Λ N k) (m : ℕ) (hm : IsUnit ((m : ℕ) : k)) :
    Finite {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f //
        nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) m P = E.L.one (𝟙 (Spec (CommRingCat.of k)))} ∧
    Nat.card {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f //
        nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) m P = E.L.one (𝟙 (Spec (CommRingCat.of k)))} = m ^ 4 := by sorry
