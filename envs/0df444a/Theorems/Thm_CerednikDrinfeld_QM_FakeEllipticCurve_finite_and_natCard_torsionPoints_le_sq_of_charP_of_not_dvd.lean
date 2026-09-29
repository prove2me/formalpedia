-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_finite_and_natCard_torsionPoints_le_sq_of_charP_of_not_dvd
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.finite_and_natCard_torsionPoints_le_sq_of_charP_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/15bcfa5d-8f0f-555d-a3b5-daa782d7cc82
-- title:
--   At most ℓ² rational ℓ-torsion points in characteristic ℓ
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$. Let $k$ be an algebraically closed field, let $\ell$ be a prime with $k$ of characteristic $\ell$, assume $\ell \nmid N$, and let $E$ be a fake elliptic curve over $k$ of type $(\Lambda,N)$, i.e. a structure consisting of a scheme $E.A$ with a morphism $E.f : E.A \to \operatorname{Spec} k$, a commutative relative group law $E.L$ on $E.f$ (functorial multiplication, unit and inverse on sections over arbitrary bases, with the group axioms and compatibility with base change), the property bundle asserting that $E.f$ is smooth and proper with connected fibres and admits a relative group law, fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms of $E.A$ over $\operatorname{Spec} k$ that is additive and multiplicative and satisfies the trace condition $\operatorname{tr}(m) = n$ whenever $m + \bar m = n$, together with further level-$N$ data. Consider the set of sections $P$ of $E.f$ over the identity of $\operatorname{Spec} k$, that is, morphisms $P : \operatorname{Spec} k \to E.A$ with $P$ followed by $E.f$ equal to the identity, such that the $\ell$-fold iterate $\ell \cdot P$ formed by repeated multiplication in $E.L$ (with $0 \cdot P$ the unit section) equals the unit section. The conclusion is that this set is finite and that its cardinality is at most $\ell^2$.
--
--   This is the bound 'the $p$-rank is at most the dimension' for the abelian surface underlying a fake elliptic curve in characteristic $\ell$: in characteristic $0$ the corresponding count is $\ell^4$, while here the group of $k$-rational $\ell$-torsion points has order at most $\ell^2$. Both conjuncts carry content, since the cardinality of an infinite type would be $0$; the result is used in the analysis of $\ell$-torsion and of level isogenies for fake elliptic curves in characteristic $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_finite_and_natCard_torsionPoints_le_sq_of_charP_of_not_dvd.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM
open CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.finite_and_natCard_torsionPoints_le_sq_of_charP_of_not_dvd
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (hℓN : ¬ ℓ ∣ N)
    (E : FakeEllipticCurve Λ N k) :
    Finite {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f //
        nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) ℓ P = E.L.one (𝟙 (Spec (CommRingCat.of k)))} ∧
      Nat.card {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f //
        nsmulPt E.L (𝟙 (Spec (CommRingCat.of k))) ℓ P = E.L.one (𝟙 (Spec (CommRingCat.of k)))} ≤ ℓ ^ 2 := by sorry
