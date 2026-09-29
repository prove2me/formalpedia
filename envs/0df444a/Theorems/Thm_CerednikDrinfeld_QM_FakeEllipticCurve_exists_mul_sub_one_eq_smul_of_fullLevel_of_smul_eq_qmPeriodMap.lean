-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_mul_sub_one_eq_smul_of_fullLevel_of_smul_eq_qmPeriodMap
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_mul_sub_one_eq_smul_of_fullLevel_of_smul_eq_qmPeriodMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/a962b9f8-1984-53a3-a3c6-8b189064e2cc
-- title:
--   Full level-m structures give units of Λ/mΛ
-- statement:
--   Fix rationals $a,b$ and write $B=\mathbb{H}[\mathbb{Q},a,b]$. Let $\Lambda\subseteq B$ be a $\mathbb{Z}$-submodule which is a maximal order, i.e. an order such that every order containing it equals it, and let $\iota\colon B\to M_2(\mathbb{R})$ be an injective $\mathbb{Q}$-algebra homomorphism. Fix $N\in\mathbb{N}$ and suppose given, for every fake elliptic curve $E$ over $\mathbb{C}$ for $(\Lambda,N)$, a $\mathbb{Z}$-submodule $\mathrm{latt}(E)\subseteq\mathbb{C}^2$ together with a bijection $e_E$ from the $\mathbb{C}$-points of $E$ (morphisms to $E.A$ over the identity of $\operatorname{Spec}\mathbb{C}$) to $\mathbb{C}^2/\mathrm{latt}(E)$, subject to: each $\mathrm{latt}(E)$ is the $\mathbb{Z}$-span of an $\mathbb{R}$-basis of $\mathbb{C}^2$ indexed by $\mathrm{Fin}\,4$ and is stable under $v\mapsto\iota(x)_{\mathbb{C}}v$ for $x\in\Lambda$; $e_E$ carries the relative group law to addition; and $e_E$ is $\Lambda$-equivariant, in the sense that $e_E(P)=[v]$ implies $e_E(x\cdot P)=[\iota(x)_{\mathbb{C}}v]$ for $x\in\Lambda$, where $x\cdot P$ is the pushforward of $P$ along the action morphism. Let $m$ be a nonzero natural number and $u=(E,\xi)$ a fake elliptic curve over $\mathbb{C}$ with a full level-$m$ structure, with underlying point $\xi.P$. Let $\tau$ lie in the upper half plane and $c\neq0$ satisfy $c\cdot\mathrm{latt}(E)=\iota(\Lambda)\binom{\tau}{1}$, the image of $\Lambda$ under $x\mapsto\iota(x)_{\mathbb{C}}\binom{\tau}{1}$. Suppose $x_0\in\Lambda$ and $v\in\mathbb{C}^2$ satisfy $e_E(\xi.P)=[v]$ and $c\,v=m^{-1}\iota(x_0)_{\mathbb{C}}\binom{\tau}{1}$. Then there is $y\in\Lambda$ with $x_0y-1\in m\Lambda$ and $yx_0-1\in m\Lambda$.
--
--   This is the step in the complex-analytic description of the moduli of fake elliptic curves which says that the label $x_0\in\Lambda$ attached, through the uniformisation $\mathbb{C}^2/\mathrm{latt}(E)$ and the period lattice $\iota(\Lambda)(\tau,1)^{\mathsf T}$, to a full level-$m$ structure is a two-sided unit modulo $m\Lambda$. It is used in the comparison of the analytic and algebraic families with extra level structure, namely by [`CerednikDrinfeld.QM.IsFineModuli.forall_exists_algebraicFamily_withExtraLevel_isPullback_smul_latt_eq_of_analytic`](thm.html#CerednikDrinfeld.QM.IsFineModuli.forall_exists_algebraicFamily_withExtraLevel_isPullback_smul_latt_eq_of_analytic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_mul_sub_one_eq_smul_of_fullLevel_of_smul_eq_qmPeriodMap.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_CerednikDrinfeld_QMFineModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_mul_sub_one_eq_smul_of_fullLevel_of_smul_eq_qmPeriodMap
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    {N : ℕ}

    (latt : FakeEllipticCurve Λ N ℂ → Submodule ℤ (Fin 2 → ℂ))
    (e : ∀ E : FakeEllipticCurve Λ N ℂ,
      SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))

    (hL1 : ∀ E : FakeEllipticCurve Λ N ℂ,
        (∃ b₀ : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), latt E = Submodule.span ℤ (Set.range b₀)) ∧
        (∀ x ∈ Λ, ∀ v ∈ latt E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ latt E))

    (hE1 : ∀ (E : FakeEllipticCurve Λ N ℂ) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f),
        e E (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e E P + e E Q)

    (hE2 : ∀ (E : FakeEllipticCurve Λ N ℂ) (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
        e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
        e E (pushPt (E.act x) (E.act_over x) P) =
          ((((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))
    (m : ℕ) [NeZero m] (u : FakeEllipticCurve.WithFullLevel Λ N m ℂ)
    (τ : UpperHalfPlane) (c : ℂ) (hc : c ≠ 0) (hlatt : c • latt u.1 = qmPeriodLattice ι Λ τ)
    (x₀ : ↥Λ) (v : Fin 2 → ℂ) (hv : e u.1 u.2.P = (v : (Fin 2 → ℂ) ⧸ (latt u.1).toAddSubgroup))
    (hx₀ : c • v = ((m : ℂ)⁻¹) • qmPeriodMap ι τ (x₀ : ℍ[ℚ, a, b])) :
    ∃ y : ↥Λ,
      (∃ z : ↥Λ, (x₀ : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (z : ℍ[ℚ, a, b])) ∧
      (∃ z : ↥Λ, (y : ℍ[ℚ, a, b]) * (x₀ : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (z : ℍ[ℚ, a, b])) := by sorry
