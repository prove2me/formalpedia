-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_forall_smul_eq_of_mem_torsionBy
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_intermediateField_finiteDimensional_forall_smul_eq_of_mem_torsionBy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/cdeb2b4d-c5b9-59c7-bb23-24796e70a8b4
-- title:
--   Finite field of definition for n-torsion of a fake elliptic curve
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a natural number $N$, and a field $K$, and let $E$ be a fake elliptic curve of type $(\Lambda,N)$ over $K$: a scheme $E.A$ with structure morphism $E.f : E.A \to \operatorname{Spec} K$ carrying a commutative relative group law $E.L$ (functorial group structure on the sets of $T$-points of $E.f$), satisfying the abelian-scheme bundle conditions (smooth, proper, connected fibres, group law), with fibres of topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms over $\operatorname{Spec} K$ subject to the multiplicativity, additivity and trace conditions, together with the auxiliary curve and level data. Let $\Omega$ be an algebraically closed field that is an algebraic extension of $K$, and let $n$ be a natural number whose image in $K$ is non-zero. Then there is an intermediate field $L$ with $K \subseteq L \subseteq \Omega$, finite-dimensional over $K$, such that: first, every $P$ in the $n$-torsion of the group $E.L.\mathrm{AlgPoints}$ of $\Omega$-points of $E.f$ over $K$ (morphisms $\operatorname{Spec}\Omega \to E.A$ composing with $E.f$ to $\operatorname{Spec}$ of $K \to \Omega$, with the group law of $E.L$, killed by $n$) is $L$-rational, i.e. there is $P' : \operatorname{Spec} L \to E.A$ with $P'$ followed by $E.f$ equal to $\operatorname{Spec}$ of $K \to L$ and with $\operatorname{Spec}$ of $L \to \Omega$ followed by $P'$ equal to the morphism underlying $P$; and second, every $K$-algebra automorphism $\sigma$ of $\Omega$ fixing $L$ pointwise fixes every such $n$-torsion point, $\sigma \cdot P = P$.
--
--   This is the statement that the field of definition of the $n$-torsion of a fake elliptic curve is a finite extension of the base field, so that the automorphism group of $\Omega$ over $K$ acts on $n$-torsion through a finite quotient. It underlies the construction and continuity of the Galois representations attached to a fake elliptic curve, and is used in the results on bases of the Tate module, on inertia acting through finite order, and on descending the $n$-torsion to a finite extension fixed by Galois.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_finiteDimensional_forall_smul_eq_of_mem_torsionBy.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAlgPointsV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
  QuaternionAlgebra
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_intermediateField_finiteDimensional_forall_smul_eq_of_mem_torsionBy
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {K : Type} [Field K] (E : FakeEllipticCurve Λ N K)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (n : ℕ) (hn : (n : K) ≠ 0) :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧
      (∀ P ∈ Submodule.torsionBy ℤ (E.L.AlgPoints E.comm Ω) (n : ℤ),
        ∃ P' : Spec (CommRingCat.of L) ⟶ E.A,
          P' ≫ E.f = Spec.map (CommRingCat.ofHom (algebraMap K L)) ∧
          Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ P' = (RelativeGroupLaw.AlgPoints.toPoint P).1) ∧
      ∀ σ : Ω ≃ₐ[K] Ω, (∀ x ∈ L, σ x = x) →
        ∀ P ∈ Submodule.torsionBy ℤ (E.L.AlgPoints E.comm Ω) (n : ℤ), σ • P = P := by sorry
