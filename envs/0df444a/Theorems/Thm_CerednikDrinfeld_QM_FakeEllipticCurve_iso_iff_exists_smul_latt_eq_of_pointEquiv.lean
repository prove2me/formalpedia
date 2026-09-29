-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_iff_exists_smul_latt_eq_of_pointEquiv
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.iso_iff_exists_smul_latt_eq_of_pointEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/2e0e8fa1-3f56-5580-acc0-fd279e6b82b7
-- title:
--   Complex fake elliptic curves: isomorphism iff homothetic lattices
-- statement:
--   Fix primes $q$ and $q'$ with $q' \neq q$ and rationals $a, b$ such that `IsIndefiniteRamifiedExactlyAt a b q q'` holds, i.e. $a > 0$ or $b > 0$ and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, the algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is an order maximal among orders containing it, and let $\iota : \mathbb{H}[\mathbb{Q},a,b] \to M_2(\mathbb{R})$ be an injective $\mathbb{Q}$-algebra map. Assume given, for every fake elliptic curve $E$ over $\mathbb{C}$ with $\Lambda$-action and level $N = 1$, a $\mathbb{Z}$-submodule $\mathrm{latt}(E) \subseteq \mathbb{C}^2$ and a bijection $e_E$ from the sections of $E.f$ over $\mathrm{id}_{\operatorname{Spec}\mathbb{C}}$ to $\mathbb{C}^2/\mathrm{latt}(E)$, subject to: $\mathrm{latt}(E)$ is the $\mathbb{Z}$-span of an $\mathbb{R}$-basis of $\mathbb{C}^2$ and is stable under $v \mapsto \iota(x)v$ for $x \in \Lambda$ (the matrix taken with complex entries); $e_E$ is additive for the relative group law; $e_E$ intertwines the action of $x \in \Lambda$ on points with multiplication by $\iota(x)$; every morphism $\varphi : E.A \to E'.A$ over $\operatorname{Spec}\mathbb{C}$ respecting the group laws on points over all bases and commuting with the $\Lambda$-actions acts on $\mathbb{C}$-points as some scalar $c$ with $c \cdot \mathrm{latt}(E) \subseteq \mathrm{latt}(E')$; conversely each such $c$ is realised by such a $\varphi$; and two morphisms over $\operatorname{Spec}\mathbb{C}$ agreeing on all such points coincide. The conclusion: for all $E, E'$ as above, `FakeEllipticCurve.Iso E E'` — an isomorphism $E.A \cong E'.A$ over $\operatorname{Spec}\mathbb{C}$ compatible with the group laws, commuting with the $\Lambda$-actions, and matching the conditions of factoring through the level maps — holds if and only if $c \cdot \mathrm{latt}(E) = \mathrm{latt}(E')$ for some $c \in \mathbb{C}^\times$.
--
--   This is the complex uniformisation criterion for fake elliptic curves: over $\mathbb{C}$, two such objects of level one are isomorphic precisely when their period lattices in $\mathbb{C}^2$ are homothetic. It is stated relative to an abstract lattice dictionary (the $\mathrm{latt}$, $e$ and Hom-description hypotheses) and is used by [`CerednikDrinfeld.QM.exists_latticeMap_fakeEllipticCurve_complex_iso_iff_smul_eq_levelOne`](thm.html#CerednikDrinfeld.QM.exists_latticeMap_fakeEllipticCurve_complex_iso_iff_smul_eq_levelOne) in the analytic description of the Shimura curve attached to the indefinite quaternion algebra ramified exactly at $q$ and $q'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_iso_iff_exists_smul_latt_eq_of_pointEquiv.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.iso_iff_exists_smul_latt_eq_of_pointEquiv
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
    (∀ E E' : FakeEllipticCurve Λ 1 ℂ,
        FakeEllipticCurve.Iso E E' ↔ ∃ c : ℂ, c ≠ 0 ∧ c • latt E = latt E') := by sorry
