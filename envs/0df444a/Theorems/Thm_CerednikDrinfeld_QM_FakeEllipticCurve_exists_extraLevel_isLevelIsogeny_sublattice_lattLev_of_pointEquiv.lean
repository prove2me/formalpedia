-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_sublattice_lattLev_of_pointEquiv
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_sublattice_lattLev_of_pointEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/34c1ec81-c7e6-5a50-8f70-b03db14c5cf3
-- title:
--   Extra levels at ℓ and admissible sublattices of the period lattice
-- statement:
--   Fix primes $q\neq q'$ and $a,b\in\mathbb{Q}$ with $\mathbb{H}[\mathbb{Q},a,b]$ indefinite ($0<a$ or $0<b$) and ramified exactly at $q,q'$ (for each finite place $v$ of $\mathbb{Q}$ the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes\mathbb{Q}_v$ is a division algebra iff $q\in v$ or $q'\in v$); let $\Lambda$ be a maximal order, $\iota$ an injective $\mathbb{Q}$-algebra map into $M_2(\mathbb{R})$, and $N\geq 1$ with $q,q'\nmid N$. Assume given the complex uniformisation dictionary for fake elliptic curves $E$ of level $N$ over $\mathbb{C}$: lattices $\mathrm{latt}\,E\subseteq\mathbb{C}^2$ spanned over $\mathbb{Z}$ by an $\mathbb{R}$-basis and stable under $\iota(\Lambda)$ acting by `mulVec`, bijections $e_E$ from the sections of $E.f$ over $\mathrm{Spec}\,\mathbb{C}$ onto $\mathbb{C}^2/\mathrm{latt}\,E$ carrying the group law to addition and the $\Lambda$-action to $\iota(\cdot)$, the description of morphisms over $\mathbb{C}$ commuting with group law and $\Lambda$-action as multiplication by scalars $c$ with $c\cdot\mathrm{latt}\,E\subseteq\mathrm{latt}\,E'$ (both directions, plus faithfulness on $\mathbb{C}$-points), and lattices $\mathrm{lattLev}\,E\supseteq\mathrm{latt}\,E$ consisting of the vectors representing points that factor through the level structure $E.\mathrm{lev}$, $\iota(\Lambda)$-stable, with $N\cdot\mathrm{lattLev}\,E\subseteq\mathrm{latt}\,E$ and $[\mathrm{lattLev}\,E:\mathrm{latt}\,E]=N^2$. The conclusion: for every prime $\ell\neq q,q'$, every $E$, every $\tau$ in the upper half-plane and every $c\neq 0$ with $c\cdot\mathrm{latt}\,E=L_\tau:=\mathrm{qmPeriodLattice}\ \iota\ \Lambda\ \tau$, there are $n$, extra level structures $K_i$ of order $\ell^2$ on $E$, fake elliptic curves $d_i$ and lattices $M_i$ ($i\in\mathrm{Fin}\ n$) such that $n=\ell$ if $\ell\mid N$ and $n=\ell+1$ otherwise; the $K_i$ are pairwise distinguished by which $\mathbb{C}$-points factor through them and every extra level structure of order $\ell^2$ on $E$ agrees pointwise with some $K_i$; each pair $(E,K_i)$ admits a level isogeny to $d_i$ in the project's sense `IsLevelIsogeny`; each $M_i$ satisfies $M_i\leq L_\tau$, $\ell L_\tau\subseteq M_i$, $\iota(\Lambda)$-stability, $[L_\tau:M_i]=\ell^2$ and the transversality condition that $v\in\mathrm{lattLev}\,E$ with $\ell c\,v\in M_i$ forces $v\in\mathrm{latt}\,E$; conversely every lattice $M'$ with those five properties equals $M_i$ for exactly one $i$; and for each $i$ there is $c_i\neq0$ with $c_i\cdot\mathrm{latt}(d_i)=M_i$ and $c_i\cdot\mathrm{lattLev}(d_i)=\ell c\cdot\mathrm{lattLev}\,E+M_i$ (stated as a membership equivalence).
--
--   This is the lattice-theoretic form of the Hecke correspondence $T_\ell$ on the moduli of fake elliptic curves with level-$N$ structure over $\mathbb{C}$: the $\ell$ or $\ell+1$ extra level structures of order $\ell^2$ on $E$ are matched bijectively with the $\iota(\Lambda)$-stable sublattices of index $\ell^2$ of the period lattice that are transversal to the level structure, together with the quotient curve and its level structure on the lattice side. It feeds the construction of the uniformised Hecke curve, being used in the statement on period maps and meromorphic realisations for uniformised Hecke curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_sublattice_lattLev_of_pointEquiv.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_sublattice_lattLev_of_pointEquiv
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
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ≠ q → ℓ ≠ q' →
        ∀ (E : FakeEllipticCurve Λ N ℂ) (τ : UpperHalfPlane) (c : ℂ), c ≠ 0 → c • latt E = qmPeriodLattice ι Λ τ →
        ∃ (n : ℕ) (K : Fin n → E.ExtraLevel ℓ) (d : Fin n → FakeEllipticCurve Λ N ℂ) (M : Fin n → Submodule ℤ (Fin 2 → ℂ)),
            (n = if ℓ ∣ N then ℓ else ℓ + 1) ∧
            (∀ i j : Fin n,
                (∀ x : SchemeHomOver (CategoryTheory.CategoryStruct.id (Spec (CommRingCat.of ℂ))) E.f,
                  FactorsThrough (K i).levK x ↔ FactorsThrough (K j).levK x) → i = j) ∧
            (∀ K' : E.ExtraLevel ℓ, ∃ i : Fin n,
                ∀ x : SchemeHomOver (CategoryTheory.CategoryStruct.id (Spec (CommRingCat.of ℂ))) E.f,
                  FactorsThrough K'.levK x ↔ FactorsThrough (K i).levK x) ∧
            (∀ i : Fin n, FakeEllipticCurve.IsLevelIsogeny ℓ
                (⟨E, K i⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ ℂ) (d i)) ∧
            (∀ i : Fin n,
              M i ≤ qmPeriodLattice ι Λ τ ∧
              (∀ v ∈ qmPeriodLattice ι Λ τ, (ℓ : ℤ) • v ∈ M i) ∧
              (∀ y ∈ Λ, ∀ v ∈ M i, ((ι y).map (algebraMap ℝ ℂ)).mulVec v ∈ M i) ∧
              (M i).toAddSubgroup.relIndex (qmPeriodLattice ι Λ τ).toAddSubgroup = ℓ ^ 2 ∧

              (∀ v ∈ lattLev E, ((ℓ : ℂ) * c) • v ∈ M i → v ∈ latt E)) ∧
            (∀ M' : Submodule ℤ (Fin 2 → ℂ),
              (M' ≤ qmPeriodLattice ι Λ τ ∧
                (∀ v ∈ qmPeriodLattice ι Λ τ, (ℓ : ℤ) • v ∈ M') ∧
                (∀ y ∈ Λ, ∀ v ∈ M', ((ι y).map (algebraMap ℝ ℂ)).mulVec v ∈ M') ∧
                M'.toAddSubgroup.relIndex (qmPeriodLattice ι Λ τ).toAddSubgroup = ℓ ^ 2 ∧
                (∀ v ∈ lattLev E, ((ℓ : ℂ) * c) • v ∈ M' → v ∈ latt E)) →
              ∃! i : Fin n, M i = M') ∧

            (∀ i : Fin n, ∃ c' : ℂ, c' ≠ 0 ∧ c' • latt (d i) = M i ∧
              ∀ v : Fin 2 → ℂ, v ∈ c' • lattLev (d i) ↔
                ∃ w ∈ lattLev E, ∃ m ∈ M i, ((ℓ : ℂ) * c) • w + m = v)) := by sorry
