-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_smul_latt_lattLev_atkinLehnerQuotient_of_pointEquiv
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_smul_latt_lattLev_atkinLehnerQuotient_of_pointEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/c25c8538-3958-59ee-9c0a-e8927d347cdf
-- title:
--   Period lattices of Atkin–Lehner quotients at level N
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ with `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$ and, for each finite place $v$ of $\mathbb{Q}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$; let $\Lambda$ be a maximal order, $\iota$ an injective $\mathbb{Q}$-algebra map to $M_2(\mathbb{R})$, and $N \neq 0$ squarefree with $q,q' \nmid N$. Assume given, for each fake elliptic curve $E$ of level $N$ over $\mathbb{C}$ (a scheme over $\operatorname{Spec}\mathbb{C}$ with commutative relative group law, abelian-scheme bundle, two-dimensional fibres, $\Lambda$-action and level map `lev`), submodules $\mathrm{latt}(E), \mathrm{lattLev}(E) \subseteq \mathbb{C}^2$ and a bijection $e_E$ from the $\mathbb{C}$-points of $E$ to $\mathbb{C}^2/\mathrm{latt}(E)$, subject to: $\mathrm{latt}(E)$ is the $\mathbb{Z}$-span of an $\mathbb{R}$-basis and is $\iota(\Lambda)$-stable; $e_E$ is additive and intertwines the $\Lambda$-action with matrix multiplication by $\iota(x)$; morphisms over $\operatorname{Spec}\mathbb{C}$ respecting the group law and commuting with $\Lambda$ correspond exactly to scalars $c$ with $c\,\mathrm{latt}(E)\subseteq\mathrm{latt}(E')$, and are determined by their effect on $\mathbb{C}$-points; $\mathrm{lattLev}(E)$ is the $e_E$-image of the points factoring through `lev`, contains $\mathrm{latt}(E)$, is $\iota(\Lambda)$-stable, satisfies $N\,\mathrm{lattLev}(E)\subseteq\mathrm{latt}(E)$ and has relative index $N^2$. Assume further an Eichler order $R$ of level $N$ with $R \le \Lambda$, and a submodule $J'$ with $\Lambda \le J'$, $\Lambda J' \subseteq J'$, $N J' \subseteq \Lambda$, relative index $N^2$, and $\{x \in \Lambda : J'x \subseteq J'\} = R$. Then for $r \in \{q,q'\}$, fake elliptic curves $E,E'$, $\tau$ in the upper half-plane and $c \neq 0$ with $c\,\mathrm{latt}(E) = \iota(\Lambda)\binom{\tau}{1}$ and $c\,\mathrm{lattLev}(E) = \iota(J')\binom{\tau}{1}$, if `E.IsAtkinLehnerQuotient r E'` holds (there are mutually $\Lambda$-equivariant group-law morphisms $\varphi : E \to E'$, $\psi : E' \to E$ over $\mathbb{C}$ composing to the action of $r$, with $\ker\varphi$ the points killed by all $m \in \Lambda$ of reduced norm divisible by $r$, and $\varphi$ carrying `lev`-points to `lev`-points), then for every $s \in R$ with $\mathrm{nrd}(s) = r$ there is $c' \neq 0$ such that $c'\,\mathrm{latt}(E')$ is the set of $\iota(ys)\binom{\tau}{1}$ with $y \in \Lambda$, and $c'\,\mathrm{lattLev}(E')$ the set of $\iota(ys)\binom{\tau}{1}$ with $y \in J'$.
--
--   This is the lattice-theoretic dictionary for the Atkin–Lehner involution at a ramified prime on the Shimura curve attached to $\Lambda$ with $\Gamma_0(N)$-type level structure: it identifies the period lattice and the level lattice of the Atkin–Lehner quotient of a uniformised fake elliptic curve with the standard pair translated by an element $s \in R$ of reduced norm $r$. It is used in the construction of period maps for meromorphic realisations on uniformised Hecke curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_smul_latt_lattLev_atkinLehnerQuotient_of_pointEquiv.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_smul_latt_lattLev_atkinLehnerQuotient_of_pointEquiv
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
      (latt E).toAddSubgroup.relIndex (lattLev E).toAddSubgroup = N ^ 2)

    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J')) :
    (∀ (r : ℕ), (r = q ∨ r = q') →
        ∀ (E E' : FakeEllipticCurve Λ N ℂ) (τ : UpperHalfPlane) (c : ℂ), c ≠ 0 →
        c • latt E = qmPeriodLattice ι Λ τ → c • lattLev E = qmPeriodLattice ι J' τ →
        E.IsAtkinLehnerQuotient r E' →
        ∀ s ∈ R, nrd s = (r : ℚ) →
          ∃ c' : ℂ, c' ≠ 0 ∧
            (∀ v : Fin 2 → ℂ, v ∈ c' • latt E' ↔ ∃ y ∈ Λ, qmPeriodMap ι τ (y * s) = v) ∧
            (∀ v : Fin 2 → ℂ, v ∈ c' • lattLev E' ↔ ∃ y ∈ J', qmPeriodMap ι τ (y * s) = v)) := by sorry
