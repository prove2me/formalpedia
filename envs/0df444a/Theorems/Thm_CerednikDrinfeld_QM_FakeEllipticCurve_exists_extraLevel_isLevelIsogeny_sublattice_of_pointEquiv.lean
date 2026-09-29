-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_sublattice_of_pointEquiv
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_sublattice_of_pointEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/e3522785-685b-595a-a2a6-09ce41e7caa9
-- title:
--   Extra levels match ι(Λ)-stable sublattices of the period lattice
-- statement:
--   Fix primes $q \ne q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for every finite place $v$ of $\mathbb{Q}$, its completion at $v$ is a division algebra exactly when $v$ lies above $q$ or $q'$; let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a maximal order (an order containing no strictly larger order) and $\iota : \mathbb{H}[\mathbb{Q},a,b] \to M_2(\mathbb{R})$ an injective $\mathbb{Q}$-algebra map. Assume the complex uniformisation dictionary for fake elliptic curves of level $1$ over $\mathbb{C}$ in the following form: an assignment $E \mapsto \operatorname{latt} E \subseteq \mathbb{C}^2$ together with bijections $e_E$ from the sections of $E.f$ over $\mathrm{id}_{\operatorname{Spec} \mathbb{C}}$ to $\mathbb{C}^2/\operatorname{latt} E$, such that each $\operatorname{latt} E$ is the $\mathbb{Z}$-span of an $\mathbb{R}$-basis of $\mathbb{C}^2$ and is stable under $v \mapsto \iota(x)v$ for $x \in \Lambda$ (hypothesis `hL1`), each $e_E$ is additive for the relative group law (`hE1`) and carries the action of $x \in \Lambda$ to multiplication by the complexification of $\iota(x)$ (`hE2`); moreover every morphism $\varphi$ over $\operatorname{Spec} \mathbb{C}$ between two such curves that respects the group laws at all bases and commutes with the $\Lambda$-actions is induced, via the $e$'s, by a scalar $c \in \mathbb{C}$ with $c \cdot \operatorname{latt} E \subseteq \operatorname{latt} E'$ (`hH1`), conversely every such scalar arises from such a $\varphi$ (`hH2`), and two morphisms agreeing on $\mathbb{C}$-points coincide (`hH3`). The conclusion is: for every prime $\ell \notin \{q,q'\}$, every fake elliptic curve $E$ of level $1$ over $\mathbb{C}$, every $\tau$ in the upper half-plane and every $c \ne 0$ with $c \cdot \operatorname{latt} E = L_\tau := \operatorname{qmPeriodLattice} \iota\, \Lambda\, \tau$ (the image of $\Lambda$ under the period map attached to $\iota$ and $\tau$), there are an $n$, a family $K : \mathrm{Fin}\, n \to E.\mathrm{ExtraLevel}\, \ell$ of extra level structures of level $\ell$ on $E$ (each a closed subscheme of $E.A$ stable under the group law, inversion and the $\Lambda$-action, killed by $\ell$, meeting $E.\mathrm{lev}$ trivially, finite flat of finite presentation of rank $\ell^2$ with geometric fibres $(\mathbb{Z}/\ell)^2$), a family $d$ of fake elliptic curves of level $1$ over $\mathbb{C}$ and a family $M$ of $\mathbb{Z}$-submodules of $\mathbb{C}^2$, with: the $K_i$ pairwise distinguished by which $\mathbb{C}$-points factor through $(K_i).\mathrm{levK}$; every extra level structure of level $\ell$ on $E$ having the same factoring points as some $K_i$; each $\langle E, K_i\rangle \to d_i$ a level isogeny in the sense of `IsLevelIsogeny` $\ell$; each $M_i$ satisfying $\ell L_\tau \subseteq M_i \subseteq L_\tau$, stability under $v \mapsto \iota(y)v$ for $y \in \Lambda$, and relative index $\ell^2$ in $L_\tau$; every submodule $M'$ with these four properties equal to $M_i$ for exactly one $i$; and, for each $i$, some $c' \ne 0$ with $c' \cdot \operatorname{latt}(d_i) = M_i$.
--
--   This is the complex-analytic dictionary for the Hecke correspondence at $\ell$ on a Shimura curve attached to an indefinite quaternion algebra ramified exactly at $q,q'$: the $\ell+1$ extra level structures of level $\ell$ on a fake elliptic curve over $\mathbb{C}$, together with the curves they map to under a level isogeny, correspond bijectively to the $\iota(\Lambda)$-stable sublattices of index $\ell^2$ between $\ell L_\tau$ and $L_\tau$. It feeds the lattice parametrisation of complex fake elliptic curves of level one used in the Čerednik–Drinfeld part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_sublattice_of_pointEquiv.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_sublattice_of_pointEquiv
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (hqq' : q' ≠ q)

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
    (hH1 : ∀ (E E' : FakeEllipticCurve Λ 1 ℂ) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
        mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
      (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) →
      ∃ c : ℂ, (∀ v ∈ latt E, c • v ∈ latt E') ∧
        ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
          e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
          e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))
    (hH2 : ∀ (E E' : FakeEllipticCurve Λ 1 ℂ) (c : ℂ), (∀ v ∈ latt E, c • v ∈ latt E') →
      ∃ (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
          mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
        (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧
        ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
          e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
          e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))
    (hH3 : ∀ (E E' : FakeEllipticCurve Λ 1 ℂ) (φ ψ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (hψ : ψ ≫ E'.f = E.f),
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f, mapPt φ hφ P = mapPt ψ hψ P) → φ = ψ) :
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ≠ q → ℓ ≠ q' →
        ∀ (E : FakeEllipticCurve Λ 1 ℂ) (τ : UpperHalfPlane) (c : ℂ), c ≠ 0 → c • latt E = qmPeriodLattice ι Λ τ →
        ∃ (n : ℕ) (K : Fin n → E.ExtraLevel ℓ) (d : Fin n → FakeEllipticCurve Λ 1 ℂ) (M : Fin n → Submodule ℤ (Fin 2 → ℂ)),
            (∀ i j : Fin n,
                (∀ x : SchemeHomOver (CategoryTheory.CategoryStruct.id (Spec (CommRingCat.of ℂ))) E.f,
                  FactorsThrough (K i).levK x ↔ FactorsThrough (K j).levK x) → i = j) ∧
            (∀ K' : E.ExtraLevel ℓ, ∃ i : Fin n,
                ∀ x : SchemeHomOver (CategoryTheory.CategoryStruct.id (Spec (CommRingCat.of ℂ))) E.f,
                  FactorsThrough K'.levK x ↔ FactorsThrough (K i).levK x) ∧
            (∀ i : Fin n, FakeEllipticCurve.IsLevelIsogeny ℓ
                (⟨E, K i⟩ : FakeEllipticCurve.WithExtraLevel Λ 1 ℓ ℂ) (d i)) ∧
            (∀ i : Fin n,
              M i ≤ qmPeriodLattice ι Λ τ ∧
              (∀ v ∈ qmPeriodLattice ι Λ τ, (ℓ : ℤ) • v ∈ M i) ∧
              (∀ y ∈ Λ, ∀ v ∈ M i, ((ι y).map (algebraMap ℝ ℂ)).mulVec v ∈ M i) ∧
              (M i).toAddSubgroup.relIndex (qmPeriodLattice ι Λ τ).toAddSubgroup = ℓ ^ 2) ∧
            (∀ M' : Submodule ℤ (Fin 2 → ℂ),
              (M' ≤ qmPeriodLattice ι Λ τ ∧
                (∀ v ∈ qmPeriodLattice ι Λ τ, (ℓ : ℤ) • v ∈ M') ∧
                (∀ y ∈ Λ, ∀ v ∈ M', ((ι y).map (algebraMap ℝ ℂ)).mulVec v ∈ M') ∧
                M'.toAddSubgroup.relIndex (qmPeriodLattice ι Λ τ).toAddSubgroup = ℓ ^ 2) →
              ∃! i : Fin n, M i = M') ∧
            (∀ i : Fin n, ∃ c' : ℂ, c' ≠ 0 ∧ c' • latt (d i) = M i)) := by sorry
