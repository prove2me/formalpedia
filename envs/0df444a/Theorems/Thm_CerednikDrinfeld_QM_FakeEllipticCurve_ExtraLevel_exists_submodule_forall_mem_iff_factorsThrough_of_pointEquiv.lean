-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_submodule_forall_mem_iff_factorsThrough_of_pointEquiv
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_submodule_forall_mem_iff_factorsThrough_of_pointEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/11030f03-22cb-5018-9903-c7d26d78fac3
-- title:
--   Period lattice attached to an extra level at ℓ
-- statement:
--   Let $q,q'$ be primes, $a,b\in\mathbb{Q}$, and let $hB$ assert that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies $0<a$ or $0<b$ and that, for a place $v$ of $\mathbb{Q}$, the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $v$ divides $q$ or $q'$. Let $\Lambda\subset\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order maximal among orders containing it, and $\iota:\mathbb{H}[\mathbb{Q},a,b]\to M_2(\mathbb{R})$ a $\mathbb{Q}$-algebra map. Assume given, for every fake elliptic curve $E$ over $\mathbb{C}$ with $\Lambda$-action and level $1$, a $\mathbb{Z}$-submodule $\mathrm{latt}(E)\subset\mathbb{C}^2$ and a bijection $e_E$ from the $\mathbb{C}$-points of $E$ (sections of $E.f$ over the identity of $\operatorname{Spec}\mathbb{C}$) to $\mathbb{C}^2/\mathrm{latt}(E)$, such that: $\mathrm{latt}(E)$ is spanned over $\mathbb{Z}$ by an $\mathbb{R}$-basis of $\mathbb{C}^2$ and is stable under $\iota(x)$ for $x\in\Lambda$; $e_E$ carries the relative group law to addition; and $e_E$ intertwines the action of $x\in\Lambda$ on points with multiplication by the matrix $\iota(x)$. Let $\ell$ be a prime, $E$ such a curve, $K$ an extra level structure of level $\ell$ on $E$ (a closed immersion $K.\mathrm{levK}:K\to E.A$ whose sections form a $\Lambda$-stable subgroup killed by $\ell$, disjoint from $E.\mathrm{lev}$, finite flat of rank $\ell^2$ with geometric fibres $\mathbb{Z}/\ell\times\mathbb{Z}/\ell$), let $\tau$ lie in the upper half-plane and $c\in\mathbb{C}^\times$ satisfy $c\cdot\mathrm{latt}(E)=\Lambda\cdot\mathrm{qmPeriodMap}(\iota,\tau)$. Then there is a $\mathbb{Z}$-submodule $L_K\subset\mathbb{C}^2$ consisting exactly of those $v$ whose class modulo $\mathrm{latt}(E)$ corresponds under $e_E^{-1}$ to a point factoring through $K.\mathrm{levK}$, with $\mathrm{latt}(E)\le L_K$, and such that $M:=(c\ell)\cdot L_K$ satisfies $M\le L_\tau$, $\ell L_\tau\subseteq M$, stability of $M$ under all $\iota(y)$ with $y\in\Lambda$, and relative index $[L_\tau:M]=\ell^2$, where $L_\tau=\mathrm{qmPeriodLattice}\,\iota\,\Lambda\,\tau$.
--
--   This is the lattice dictionary for extra level structures on fake elliptic curves: an extra level at $\ell$ on a complex fake elliptic curve corresponds to a $\iota(\Lambda)$-stable lattice sandwiched between $\ell L_\tau$ and $L_\tau$ of index $\ell^2$. It feeds the construction of extra levels from such sublattices used in the analytic description of Shimura curves with $\Gamma_0(\ell)$-type level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_submodule_forall_mem_iff_factorsThrough_of_pointEquiv.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise

theorem CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_submodule_forall_mem_iff_factorsThrough_of_pointEquiv
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ)

    (latt : FakeEllipticCurve Λ 1 ℂ → Submodule ℤ (Fin 2 → ℂ))
    (e : ∀ E : FakeEllipticCurve Λ 1 ℂ,
      SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))
    (hL1 : ∀ E : FakeEllipticCurve Λ 1 ℂ,
      (∃ b₀ : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), latt E = Submodule.span ℤ (Set.range b₀)) ∧
      (∀ x ∈ Λ, ∀ v ∈ latt E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ latt E))
    (hE1 : ∀ (E : FakeEllipticCurve Λ 1 ℂ) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f),
      e E (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e E P + e E Q)
    (hE2 : ∀ (E : FakeEllipticCurve Λ 1 ℂ) (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
      e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
      e E (pushPt (E.act x) (E.act_over x) P) =
        ((((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (E : FakeEllipticCurve Λ 1 ℂ) (K : E.ExtraLevel ℓ)
    (τ : UpperHalfPlane) (c : ℂ) (hc : c ≠ 0) (hcL : c • latt E = qmPeriodLattice ι Λ τ) :
    ∃ LK : Submodule ℤ (Fin 2 → ℂ),
      (∀ v : Fin 2 → ℂ, v ∈ LK ↔ FactorsThrough K.levK ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))) ∧
      latt E ≤ LK ∧
      (c * ℓ) • LK ≤ qmPeriodLattice ι Λ τ ∧
      (∀ v ∈ qmPeriodLattice ι Λ τ, (ℓ : ℤ) • v ∈ (c * ℓ) • LK) ∧
      (∀ y ∈ Λ, ∀ v ∈ (c * ℓ) • LK, ((ι y).map (algebraMap ℝ ℂ)).mulVec v ∈ (c * ℓ) • LK) ∧
      ((c * ℓ) • LK).toAddSubgroup.relIndex (qmPeriodLattice ι Λ τ).toAddSubgroup = ℓ ^ 2 := by sorry
