-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_tateModule_forall_generator_torsion_of_isMaximalOrder_of_prime
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_tateModule_forall_generator_torsion_of_isMaximalOrder_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/2b96a6c1-99db-57e9-b2fc-85f80984741c
-- title:
--   Compatible Λ-generators of the ℓ-adic Tate module
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $q,q'$ be primes such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $a>0$ or $b>0$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all its nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order, in the sense that it is an order and every order containing it equals it, let $N\in\mathbb{N}$, let $K$ be an algebraically closed field, and let $E$ be a fake elliptic curve of level $N$ for $\Lambda$ over $K$: a scheme $E.A$ with a structure morphism $E.f$ to $\operatorname{Spec}K$ carrying a commutative relative group law $E.L$, an abelian-scheme property bundle, fibres of dimension $2$, an action $m\mapsto E.act\,m$ of $\Lambda$ by endomorphisms over $\operatorname{Spec}K$ compatible with the group law, additive in $m$ and satisfying the trace condition, together with the level data. Let $\ell$ be a prime with $\ell\neq 0$ in $K$. Then there is an element $x$ of the $\ell$-adic Tate module of the group $A(K)=E.L.AlgPoints\,E.comm\,K$ of $K$-points, that is, a sequence $(x_n)_{n\ge 0}$ of $K$-points with $\ell^n\cdot x_n=0$ and $\ell\cdot x_{n+1}=x_n$, such that for every $n$: first, every $K$-point $P$ with $\ell^n\cdot P=0$ is of the form $P=E.act\,m$ applied to $x_n$ for some $m\in\Lambda$; and second, for $m\in\Lambda$, the point $E.act\,m$ applied to $x_n$ is the identity section of $E.L$ over $\operatorname{Spec}K$ if and only if $m=\ell^n m'$ in $\mathbb{H}[\mathbb{Q},a,b]$ for some $m'\in\Lambda$.
--
--   This is the generator form of the statement that the $\ell$-adic Tate module of a fake elliptic curve is free of rank one over $\Lambda\otimes\mathbb{Z}_\ell$ when $\ell$ is invertible in the base field: the components $x_n$ generate $A(K)[\ell^n]$ over $\Lambda$ with annihilator exactly $\ell^n\Lambda$, compatibly under multiplication by $\ell$. It feeds the corresponding assertion phrased directly in terms of the group of algebraic points, [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_tateModule_algPoints_forall_generator_torsion_of_isMaximalOrder_of_prime`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_tateModule_algPoints_forall_generator_torsion_of_isMaximalOrder_of_prime), and through it the analysis of torsion and Tate modules of fake elliptic curves in the Čerednik–Drinfel'd setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_tateModule_forall_generator_torsion_of_isMaximalOrder_of_prime.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAlgPointsV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
  QuaternionAlgebra
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_tateModule_forall_generator_torsion_of_isMaximalOrder_of_prime
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ}
    (K : Type) [Field K] [IsAlgClosed K] (E : FakeEllipticCurve Λ N K)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓK : (ℓ : K) ≠ 0) :
    ∃ x : TateModule ℓ (E.L.AlgPoints E.comm K),
      ∀ n : ℕ,
        (∀ P : E.L.AlgPoints E.comm K, ℓ ^ n • P = 0 →
          ∃ m : ↥Λ, RelativeGroupLaw.AlgPoints.toPoint P =
            pushPt (E.act m) (E.act_over m) (RelativeGroupLaw.AlgPoints.toPoint ((x : ℕ → E.L.AlgPoints E.comm K) n))) ∧
        (∀ m : ↥Λ,
          pushPt (E.act m) (E.act_over m) (RelativeGroupLaw.AlgPoints.toPoint ((x : ℕ → E.L.AlgPoints E.comm K) n)) =
              E.L.one (Spec.map (CommRingCat.ofHom (algebraMap K K))) ↔
            ∃ m' : ↥Λ, (m : ℍ[ℚ, a, b]) = (((ℓ ^ n : ℕ) : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b])) := by sorry
