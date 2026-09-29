-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_smul_mem_of_transversal_of_pointEquiv
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_smul_mem_of_transversal_of_pointEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/b22acc71-6e2c-58d4-bde4-37a020ba8321
-- title:
--   Extra level-ℓ structure from a transversal sublattice
-- statement:
--   Fix primes $q,q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$; fix a maximal order $\Lambda$ (an order contained in no strictly larger order), a $\mathbb{Q}$-algebra map $\iota:\mathbb{H}[\mathbb{Q},a,b]\to M_2(\mathbb{R})$ and $N\in\mathbb{N}$. Suppose given, for every fake elliptic curve $E$ of level $N$ over $\mathbb{C}$ (in the sense of `FakeEllipticCurve`), a $\mathbb{Z}$-submodule $\mathrm{latt}\,E\subseteq\mathbb{C}^2$ and a bijection $e_E$ from the sections of $E.f$ over $\mathrm{id}_{\operatorname{Spec}\mathbb{C}}$ onto $\mathbb{C}^2/\mathrm{latt}\,E$, such that: $\mathrm{latt}\,E$ is the $\mathbb{Z}$-span of an $\mathbb{R}$-basis of $\mathbb{C}^2$ and is stable under $v\mapsto\iota(x)v$ for $x\in\Lambda$; $e_E$ carries $E.L.\mathrm{mul}$ to addition; and $e_E$ carries the action of $x\in\Lambda$ to multiplication by $\iota(x)$ on representatives. Suppose also given submodules $\mathrm{lattLev}\,E$ consisting of the classes of points factoring through the level map $E.\mathrm{lev}$, containing $\mathrm{latt}\,E$, $\iota(\Lambda)$-stable, killed by $N$ modulo $\mathrm{latt}\,E$, with relative index $N^2$ over $\mathrm{latt}\,E$. Let $\ell$ be prime, $E$ such a curve, $\tau$ in the upper half-plane and $c\neq0$ with $c\cdot\mathrm{latt}\,E=L_\tau:=\iota(\Lambda)$-image of $\Lambda$ under `qmPeriodMap`. Let $M'\subseteq L_\tau$ be $\iota(\Lambda)$-stable with $\ell L_\tau\subseteq M'$, relative index $\ell^2$ in $L_\tau$, and transversal to the level in the sense that $v\in\mathrm{lattLev}\,E$ and $\ell c\,v\in M'$ force $v\in\mathrm{latt}\,E$. Then there exists an `ExtraLevel` $K$ of $E$ at $\ell$ — a closed subscheme $K\to E.A$, closed under the group law, inverse and identity, killed by $\ell$, $\Lambda$-stable, meeting $E.\mathrm{lev}$ only in the identity, finite flat of finite presentation of rank $\ell^2$ over the base with geometric fibres $(\mathbb{Z}/\ell)^2$ — such that for all $v\in\mathbb{C}^2$ the point $e_E^{-1}(v\bmod\mathrm{latt}\,E)$ factors through $K.\mathrm{levK}$ if and only if $(c\ell)v\in M'$.
--
--   This is the converse half of the lattice dictionary for extra level-$\ell$ structures on fake elliptic curves: every sublattice of the quaternionic period lattice that is admissible and transversal to the given level structure is realised by a genuine $\Lambda$-stable subgroup scheme of rank $\ell^2$. It feeds the construction of level-$\ell$ isogenies between fake elliptic curves and the associated Hecke correspondences on Shimura curves in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_smul_mem_of_transversal_of_pointEquiv.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_smul_mem_of_transversal_of_pointEquiv
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) {N : ℕ}

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

    (lattLev : FakeEllipticCurve Λ N ℂ → Submodule ℤ (Fin 2 → ℂ))
    (hLev : ∀ E : FakeEllipticCurve Λ N ℂ,
      (∀ v : Fin 2 → ℂ, v ∈ lattLev E ↔
        ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
          FactorsThrough E.lev P ∧ e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) ∧
      latt E ≤ lattLev E ∧
      (∀ x ∈ Λ, ∀ v ∈ lattLev E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ lattLev E) ∧
      (∀ v ∈ lattLev E, (N : ℤ) • v ∈ latt E) ∧
      (latt E).toAddSubgroup.relIndex (lattLev E).toAddSubgroup = N ^ 2)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (E : FakeEllipticCurve Λ N ℂ)
    (τ : UpperHalfPlane) (c : ℂ) (hc : c ≠ 0) (hcL : c • latt E = qmPeriodLattice ι Λ τ)

    (M' : Submodule ℤ (Fin 2 → ℂ))
    (hM' : M' ≤ qmPeriodLattice ι Λ τ ∧
      (∀ v ∈ qmPeriodLattice ι Λ τ, (ℓ : ℤ) • v ∈ M') ∧
      (∀ y ∈ Λ, ∀ v ∈ M', ((ι y).map (algebraMap ℝ ℂ)).mulVec v ∈ M') ∧
      M'.toAddSubgroup.relIndex (qmPeriodLattice ι Λ τ).toAddSubgroup = ℓ ^ 2 ∧
      (∀ v ∈ lattLev E, ((ℓ : ℂ) * c) • v ∈ M' → v ∈ latt E)) :
    ∃ K : E.ExtraLevel ℓ, ∀ v : Fin 2 → ℂ,
      FactorsThrough K.levK ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) ↔ (c * ℓ) • v ∈ M' := by sorry
