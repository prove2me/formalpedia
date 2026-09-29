-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_latticeMap_pointEquiv_quotient_hom_iff_smul_le_levelOne
-- name    : CerednikDrinfeld.QM.exists_latticeMap_pointEquiv_quotient_hom_iff_smul_le_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/0fa9fd47-3ce9-519e-9ea4-2ab3ec105a88
-- title:
--   Period lattices of level-one fake elliptic curves over ℂ
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$ and let $a,b\in\mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: $a>0$ or $b>0$, and for every height-one prime $v$ of the integers of $\mathbb{Q}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subset\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule that is a maximal order (it contains $1$, is closed under multiplication, spans the algebra over $\mathbb{Q}$, is finitely generated, and any order containing it equals it), and let $\iota$ be an injective $\mathbb{Q}$-algebra map $\mathbb{H}[\mathbb{Q},a,b]\to M_2(\mathbb{R})$. Then there are an assignment $E\mapsto \mathrm{latt}(E)$ of a $\mathbb{Z}$-submodule of $\mathbb{C}^2$ to each $E:$ `FakeEllipticCurve Λ 1 ℂ` (a scheme $E.A$ over $\operatorname{Spec}\mathbb{C}$ carrying a commutative relative group law $E.L$, the smoothness/properness/connected-fibre bundle, two-dimensional fibres, and an action $E.\mathrm{act}$ of $\Lambda$ by endomorphisms over the base with the structure's compatibilities), and bijections $e_E$ from the sections of $E.f$ over $\mathbb{1}_{\operatorname{Spec}\mathbb{C}}$ onto $\mathbb{C}^2/\mathrm{latt}(E)$, such that: (i) $\mathrm{latt}(E)$ is the $\mathbb{Z}$-span of an $\mathbb{R}$-basis of $\mathbb{C}^2$ indexed by $\mathrm{Fin}\,4$ and is stable under $\mathrm{mulVec}$ by the complexification of $\iota(x)$ for all $x\in\Lambda$; (ii) $e_E$ carries $E.L.\mathrm{mul}$ to addition; (iii) $e_E$ is $\Lambda$-equivariant, $e_E$ of the push-forward of $P$ by $E.\mathrm{act}\,x$ being the class of $\iota(x)_{\mathbb{C}}\cdot v$ whenever $e_E(P)$ is the class of $v$; (iv) every $\varphi: E.A\to E'.A$ with $\varphi\ \text{followed by}\ E'.f = E.f$ that respects the group laws on $T$-points for all $T$ and satisfies $E.\mathrm{act}\,x$ followed by $\varphi$ equal to $\varphi$ followed by $E'.\mathrm{act}\,x$ acts through some $c\in\mathbb{C}$ with $c\,\mathrm{latt}(E)\subseteq\mathrm{latt}(E')$, i.e. $e_{E'}(\varphi\circ P)$ is the class of $c\,v$; (v) conversely every $c\in\mathbb{C}$ with $c\,\mathrm{latt}(E)\subseteq\mathrm{latt}(E')$ arises from such a $\varphi$; (vi) two morphisms over the base inducing the same map on these $\mathbb{C}$-points coincide.
--
--   This is the uniformisation dictionary for fake elliptic curves of level one over $\mathbb{C}$: their $\mathbb{C}$-points are complex tori $\mathbb{C}^2/L$ with $L$ a lattice stable under a maximal order $\Lambda$, $\Lambda$-equivariant homomorphisms correspond to homotheties carrying one lattice into the other, and homomorphisms are determined on $\mathbb{C}$-points. It supplies the analytic input for the classification of complex fake elliptic curves up to isomorphism by homothety classes of $\iota(\Lambda)$-stable lattices, which cites it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_latticeMap_pointEquiv_quotient_hom_iff_smul_le_levelOne.lean

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

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open AlgebraicCurve
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise

theorem CerednikDrinfeld.QM.exists_latticeMap_pointEquiv_quotient_hom_iff_smul_le_levelOne
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (hqq' : q' ≠ q) :
    ∃ (latt : FakeEllipticCurve Λ 1 ℂ → Submodule ℤ (Fin 2 → ℂ))
      (e : ∀ E : FakeEllipticCurve Λ 1 ℂ,
        SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)),

      (∀ E : FakeEllipticCurve Λ 1 ℂ,
        (∃ b₀ : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), latt E = Submodule.span ℤ (Set.range b₀)) ∧
        (∀ x ∈ Λ, ∀ v ∈ latt E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ latt E)) ∧

      (∀ (E : FakeEllipticCurve Λ 1 ℂ) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f),
        e E (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e E P + e E Q) ∧

      (∀ (E : FakeEllipticCurve Λ 1 ℂ) (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
        e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
        e E (pushPt (E.act x) (E.act_over x) P) =
          ((((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) ∧

      (∀ (E E' : FakeEllipticCurve Λ 1 ℂ) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
          mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
        (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) →
        ∃ c : ℂ, (∀ v ∈ latt E, c • v ∈ latt E') ∧
          ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
            e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
            e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup)) ∧

      (∀ (E E' : FakeEllipticCurve Λ 1 ℂ) (c : ℂ), (∀ v ∈ latt E, c • v ∈ latt E') →
        ∃ (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
            mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
          (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧
          ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
            e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
            e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup)) ∧

      (∀ (E E' : FakeEllipticCurve Λ 1 ℂ) (φ ψ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (hψ : ψ ≫ E'.f = E.f),
        (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f, mapPt φ hφ P = mapPt ψ hψ P) → φ = ψ) := by sorry
