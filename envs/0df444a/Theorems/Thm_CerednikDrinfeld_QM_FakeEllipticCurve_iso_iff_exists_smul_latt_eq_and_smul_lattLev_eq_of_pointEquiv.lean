-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_iff_exists_smul_latt_eq_and_smul_lattLev_eq_of_pointEquiv
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.iso_iff_exists_smul_latt_eq_and_smul_lattLev_eq_of_pointEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/29205a3f-d8b9-58bd-acbf-8260bb5c1cf2
-- title:
--   Isomorphism of level-N fake elliptic curves as lattice homothety
-- statement:
--   Fix primes $q,q'$ with $q'\neq q$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, let $\iota$ be an injective $\mathbb{Q}$-algebra map $\mathbb{H}[\mathbb{Q},a,b]\to M_2(\mathbb{R})$, and let $N\neq 0$ be prime to $q$ and $q'$. Assume given, for every $E$ of type `FakeEllipticCurve Λ N ℂ`, a $\mathbb{Z}$-submodule $\mathrm{latt}\,E\subseteq\mathbb{C}^2$ and a bijection $e_E$ from the sections of `E.f` over $\mathrm{Spec}\,\mathbb{C}$ to $\mathbb{C}^2/\mathrm{latt}\,E$, subject to: $\mathrm{latt}\,E$ is the $\mathbb{Z}$-span of an $\mathbb{R}$-basis of $\mathbb{C}^2$ and is stable under $\iota(x)$ for $x\in\Lambda$ (hL1); $e_E$ is additive for `E.L.mul` (hE1) and turns `E.act x` into multiplication by $\iota(x)$ (hE2); every morphism $E.A\to E'.A$ over $\mathrm{Spec}\,\mathbb{C}$ compatible with the group laws on all test schemes and commuting with the $\Lambda$-actions is multiplication by some $c\in\mathbb{C}$ with $c\cdot\mathrm{latt}\,E\subseteq\mathrm{latt}\,E'$ (hH1), conversely each such $c$ comes from such a morphism (hH2), and morphisms agreeing on $\mathbb{C}$-points coincide (hH3); and a second submodule $\mathrm{lattLev}\,E$ whose classes mod $\mathrm{latt}\,E$ are exactly the $e_E(P)$ with $P$ factoring through `E.lev`, containing $\mathrm{latt}\,E$, $\iota(\Lambda)$-stable, with $N\cdot\mathrm{lattLev}\,E\subseteq\mathrm{latt}\,E$ and relative index $N^2$ (hLev). The conclusion is that for all $E,E'$, `FakeEllipticCurve.Iso E E'` — an isomorphism $E.A\cong E'.A$ over $\mathrm{Spec}\,\mathbb{C}$ respecting the group laws and the $\Lambda$-actions and matching factorisation through `E.lev` and `E'.lev` for points over all test schemes — holds if and only if there is $c\in\mathbb{C}$, $c\neq 0$, with $c\cdot\mathrm{latt}\,E=\mathrm{latt}\,E'$ and $c\cdot\mathrm{lattLev}\,E=\mathrm{lattLev}\,E'$.
--
--   This is the classical transcendental dictionary for quaternionic multiplication abelian surfaces with level-$N$ structure: over $\mathbb{C}$, isomorphism classes of fake elliptic curves with level structure correspond to homothety classes of pairs of $\iota(\Lambda)$-stable lattices in $\mathbb{C}^2$. It is used in the construction and analysis of the Shimura curve moduli problem, for instance in the integrality of the coarse moduli space over $\mathbb{C}$ and in the local charts for the period map on the fine moduli space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_iff_exists_smul_latt_eq_and_smul_lattLev_eq_of_pointEquiv.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.iso_iff_exists_smul_latt_eq_and_smul_lattLev_eq_of_pointEquiv
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (hqq' : q' ≠ q)
    {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)

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
    (hH1 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
        mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
      (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) →
      ∃ c : ℂ, (∀ v ∈ latt E, c • v ∈ latt E') ∧
        ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
          e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
          e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))
    (hH2 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (c : ℂ), (∀ v ∈ latt E, c • v ∈ latt E') →
      ∃ (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
          mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
        (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧
        ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
          e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
          e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))
    (hH3 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (φ ψ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (hψ : ψ ≫ E'.f = E.f),
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f, mapPt φ hφ P = mapPt ψ hψ P) → φ = ψ)

    (lattLev : FakeEllipticCurve Λ N ℂ → Submodule ℤ (Fin 2 → ℂ))
    (hLev : ∀ E : FakeEllipticCurve Λ N ℂ,
      (∀ v : Fin 2 → ℂ, v ∈ lattLev E ↔
        ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
          FactorsThrough E.lev P ∧ e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) ∧
      latt E ≤ lattLev E ∧
      (∀ x ∈ Λ, ∀ v ∈ lattLev E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ lattLev E) ∧
      (∀ v ∈ lattLev E, (N : ℤ) • v ∈ latt E) ∧
      (latt E).toAddSubgroup.relIndex (lattLev E).toAddSubgroup = N ^ 2) :
    (∀ E E' : FakeEllipticCurve Λ N ℂ,
        FakeEllipticCurve.Iso E E' ↔
          ∃ c : ℂ, c ≠ 0 ∧ c • latt E = latt E' ∧ c • lattLev E = lattLev E') := by sorry
