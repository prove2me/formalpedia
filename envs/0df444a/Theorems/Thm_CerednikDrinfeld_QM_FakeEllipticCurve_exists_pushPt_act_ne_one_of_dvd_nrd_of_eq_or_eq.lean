-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/cec79e70-c4b3-5103-8caf-7353bbd5f1f5
-- title:
--   A ramified prime ideal acts nontrivially on r-torsion
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $q,q'$ be primes, and assume `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $a>0$ or $b>0$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the algebra $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb{Q}_v$ has all its nonzero elements invertible exactly when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order: it contains $1$, is closed under multiplication, is finitely generated, spans the algebra over $\mathbb{Q}$, and no strictly larger $\mathbb{Z}$-submodule with these properties contains it. Let $N\in\mathbb{N}$, let $K$ be an algebraically closed field, and let $E$ be a fake elliptic curve of level $N$ with $\Lambda$-action over $K$, i.e. a smooth proper scheme $E.f : A \to \operatorname{Spec} K$ with connected fibres of dimension $2$, a commutative relative group law $E.L$, an action $x \mapsto E.\mathrm{act}\,x$ of $\Lambda$ by endomorphisms over $K$ compatible with the group law and with a trace condition, together with the further level data recorded in the structure. Let $r\in\mathbb{N}$ with $r=q$ or $r=q'$, and assume $r\neq 0$ in $K$. Then there exist a $K$-point $P$ of $A$ (a morphism $\operatorname{Spec} K \to A$ over the identity of $\operatorname{Spec} K$) and an element $x\in\Lambda$ such that the $r$-fold sum of $P$ for $E.L$ is the unit section, the reduced norm $\mathrm{nrd}(x)$ equals $r$ times an integer, and the image of $P$ under the endomorphism $E.\mathrm{act}\,x$ is not the unit section.
--
--   This is the faithfulness statement for the two-sided ideal $\mathfrak P_r=\{x\in\Lambda : r\mid \mathrm{nrd}(x)\}$ of a maximal order above a ramified prime $r$: it does not annihilate the $r$-torsion of a fake elliptic curve in residue characteristic different from $r$. It feeds into [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_generator_torsionPoints_of_isMaximalOrder_of_prime`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_generator_torsionPoints_of_isMaximalOrder_of_prime), where, combined with the count $\#A[r](K)=r^{4}$, it yields that $A[r](K)$ is free of rank one over $\Lambda/r\Lambda$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_QuaternionAlgebra_ReducedNorm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped Quaternion
open CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_pushPt_act_ne_one_of_dvd_nrd_of_eq_or_eq
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ}
    (K : Type) [Field K] [IsAlgClosed K] (E : FakeEllipticCurve Λ N K)
    (r : ℕ) (hr : r = q ∨ r = q') (hrK : (r : K) ≠ 0) :
    ∃ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) E.f) (x : ↥Λ),
      nsmulPt E.L (𝟙 (Spec (CommRingCat.of K))) r P = E.L.one (𝟙 (Spec (CommRingCat.of K))) ∧
      (∃ n : ℤ, nrd (x : ℍ[ℚ, a, b]) = (r : ℚ) * n) ∧
      pushPt (E.act x) (E.act_over x) P ≠ E.L.one (𝟙 (Spec (CommRingCat.of K))) := by sorry
