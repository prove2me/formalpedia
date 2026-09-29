-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_tateModule_algPoints_forall_generator_torsion_of_isMaximalOrder_of_prime
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_tateModule_algPoints_forall_generator_torsion_of_isMaximalOrder_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/4286abf3-0f0c-517d-b6aa-0b6309f32f36
-- title:
--   Free rank-one Tate module of a fake elliptic curve
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $q,q'$ be primes such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`: $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra (every non-zero element is a unit) exactly when $q$ or $q'$ lies in $v$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order, i.e. an order that is maximal among orders containing it, let $N\in\mathbb{N}$, let $K$ be a field and let $E$ be a fake elliptic curve over $K$ with $\Lambda$-action and level-$N$ data (`FakeEllipticCurve`): a scheme $E.A$ with structure morphism $E.f$ to $\operatorname{Spec}K$, a commutative relative group law $E.L$ with the abelian-scheme property bundle and two-dimensional fibres, and endomorphisms $E.\mathrm{act}(m)$ over $\operatorname{Spec}K$ for $m\in\Lambda$ realising the $\Lambda$-action. Let $\Omega$ be an algebraically closed field which is a $K$-algebra and let $\ell$ be a prime with $\ell\neq 0$ in $K$. Then there exists an element $x$ of the $\ell$-adic Tate module of the group $E.L.\mathrm{AlgPoints}$ of $\Omega$-points of $E$ over $K$ — a sequence $(x_n)_{n}$ of such points with $\ell^n x_n=0$ and $\ell\, x_{n+1}=x_n$ — such that for every $n$: (1) every $\Omega$-point $P$ with $\ell^n\cdot P=0$ is of the form $P=E.\mathrm{act}(m)\circ x_n$ for some $m\in\Lambda$; and (2) for $m\in\Lambda$, the point $E.\mathrm{act}(m)\circ x_n$ equals the neutral section $E.L.\mathrm{one}$ over $\operatorname{Spec}\Omega\to\operatorname{Spec}K$ if and only if $m=\ell^n m'$ in $\mathbb{H}[\mathbb{Q},a,b]$ for some $m'\in\Lambda$.
--
--   Conditions (1) and (2) say that $x_n$ generates the $\ell^n$-torsion of $E(\Omega)$ as a $\Lambda$-module with annihilator exactly $\ell^n\Lambda$, compatibly in $n$; equivalently, $m\mapsto m\,x$ identifies $\Lambda\otimes\mathbb{Z}_\ell$ with the $\ell$-adic Tate module, which is therefore free of rank one over $\Lambda\otimes\mathbb{Z}_\ell$. This is the version over an arbitrary base field $K$, with points taken in an algebraically closed extension $\Omega$, of the corresponding statement over an algebraically closed field, and it is the module-theoretic input for the $\ell$-adic Galois representations attached to fake elliptic curves: it is used in the construction of a $\Lambda\otimes\mathbb{Z}_\ell$-basis of the Tate module and in the analysis of the action of inertia on torsion points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_tateModule_algPoints_forall_generator_torsion_of_isMaximalOrder_of_prime.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_tateModule_algPoints_forall_generator_torsion_of_isMaximalOrder_of_prime
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ}
    {K : Type} [Field K] (E : FakeEllipticCurve Λ N K)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓK : (ℓ : K) ≠ 0) :
    ∃ x : TateModule ℓ (E.L.AlgPoints E.comm Ω),
      ∀ n : ℕ,
        (∀ P : E.L.AlgPoints E.comm Ω, ℓ ^ n • P = 0 →
          ∃ m : ↥Λ, RelativeGroupLaw.AlgPoints.toPoint P =
            pushPt (E.act m) (E.act_over m) (RelativeGroupLaw.AlgPoints.toPoint ((x : ℕ → E.L.AlgPoints E.comm Ω) n))) ∧
        (∀ m : ↥Λ,
          pushPt (E.act m) (E.act_over m) (RelativeGroupLaw.AlgPoints.toPoint ((x : ℕ → E.L.AlgPoints E.comm Ω) n)) =
              E.L.one (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ↔
            ∃ m' : ↥Λ, (m : ℍ[ℚ, a, b]) = (((ℓ ^ n : ℕ) : ℚ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b])) := by sorry
