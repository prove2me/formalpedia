-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_latticeMap_pointEquiv_hom_iff_smul_le_analytic
-- name    : CerednikDrinfeld.QM.exists_latticeMap_pointEquiv_hom_iff_smul_le_analytic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/816c62ab-bf31-55fa-832e-7ebe9f0d6aec
-- title:
--   Analytic uniformisation of fake elliptic curves over ℂ
-- statement:
--   Fix primes $q,q'$ with $q'\neq q$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for every finite place $v$ of $\mathbb{Q}$, its completion at $v$ is a division algebra exactly when $v$ lies above $q$ or above $q'$; fix $\Lambda$, a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is an order (contains $1$, is closed under multiplication, spans the algebra over $\mathbb{Q}$ and is finitely generated) and is maximal among orders containing it; fix an injective $\mathbb{Q}$-algebra map $\iota:\mathbb{H}[\mathbb{Q},a,b]\to M_2(\mathbb{R})$; and fix a nonzero natural number $N$ divisible by neither $q$ nor $q'$. Then there are an assignment $E\mapsto \mathrm{latt}(E)$, a $\mathbb{Z}$-submodule of $\mathbb{C}^2$, and bijections $e_E$ from the $\mathbb{C}$-points of $E$ (sections of the structure morphism $E.f$ over the identity of $\operatorname{Spec}\mathbb{C}$) to $\mathbb{C}^2/\mathrm{latt}(E)$, defined for all objects $E$ of `FakeEllipticCurve` $\Lambda$ $N$ $\mathbb{C}$ — that is, schemes $A$ with a morphism $f$ to $\operatorname{Spec}\mathbb{C}$, a commutative relative group law $L$, the abelian-scheme property bundle (smooth, proper, connected fibres, a group law existing), fibres of topological Krull dimension $2$, an action $x\mapsto E.\mathrm{act}\,x$ of $\Lambda$ by endomorphisms over the base which is additive, multiplicative, compatible with $L$ on points and satisfies the trace condition on tangent vectors, together with the remaining level-$N$ data of that structure — such that: (i) each $\mathrm{latt}(E)$ is the $\mathbb{Z}$-span of an $\mathbb{R}$-basis of $\mathbb{C}^2$ indexed by $\mathrm{Fin}\,4$, and is stable under multiplication by the matrices $\iota(x)$, $x\in\Lambda$, with entries pushed into $\mathbb{C}$; (ii) $e_E$ carries $L$-multiplication of $\mathbb{C}$-points to addition; (iii) $e_E$ is $\Lambda$-equivariant: if $e_E(P)$ is the class of $v$, then $e_E$ of the image of $P$ under $E.\mathrm{act}\,x$ is the class of $\iota(x)v$; (iv) every morphism $\varphi:E.A\to E'.A$ over $\operatorname{Spec}\mathbb{C}$ which is additive on points over every base and commutes with the $\Lambda$-actions is given by a scalar $c\in\mathbb{C}$ with $c\,\mathrm{latt}(E)\subseteq\mathrm{latt}(E')$, in the sense that $e_{E'}(P\circ\varphi)$ is the class of $cv$ whenever $e_E(P)$ is the class of $v$; (v) conversely every such $c$ arises from some additive, $\Lambda$-equivariant $\varphi$ over $\operatorname{Spec}\mathbb{C}$; (vi) two morphisms $E.A\to E'.A$ over $\operatorname{Spec}\mathbb{C}$ agreeing on all $\mathbb{C}$-points are equal; (vii) for every open $U\subseteq E.A$ and every $f\in\Gamma(E.A,U)$, the set of $v\in\mathbb{C}^2$ whose point $e_E^{-1}([v])$ factors through $U$ is open, and there is $F:\mathbb{C}^2\to\mathbb{C}$, holomorphic on that set, whose value at such $v$ is the value of $f$ at $e_E^{-1}([v])$ (transported along the canonical isomorphism $\Gamma(\operatorname{Spec}\mathbb{C})\cong\mathbb{C}$); and (viii) for every $E$ and every $v_0\in\mathbb{C}^2$ there are an open $U\subseteq E.A$, two sections $f_1,f_2\in\Gamma(E.A,U)$, a radius $\varepsilon>0$, a continuous $\mathbb{C}$-linear automorphism $D$ of $\mathbb{C}^2$ and a map $F:\mathbb{C}^2\to\mathbb{C}^2$ such that all points $e_E^{-1}([v])$ with $v$ in the ball of radius $\varepsilon$ about $v_0$ factor through $U$, on that ball $F$ is given by the pair of values of $f_1$ and $f_2$ at $e_E^{-1}([v])$, and $F$ has Fréchet derivative $D$ at $v_0$.
--
--   This is the complex-analytic uniformisation of fake elliptic curves with quaternionic multiplication by a maximal order and level-$N$ structure: each becomes a complex torus $\mathbb{C}^2/L$ with $\iota(\Lambda)$-stable lattice, morphisms correspond exactly to homotheties $c$ with $cL\subseteq L'$, and the uniformisation is pinned by the holomorphy clauses (vii)–(viii), which rule out non-holomorphic additive $\Lambda$-equivariant reparametrisations. It supports the integrality statements for the coarse moduli schemes of such curves over $\mathbb{C}$ and the corresponding level-one assertion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_latticeMap_pointEquiv_hom_iff_smul_le_analytic.lean

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

theorem CerednikDrinfeld.QM.exists_latticeMap_pointEquiv_hom_iff_smul_le_analytic
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (hqq' : q' ≠ q)
    {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) :
    ∃ (latt : FakeEllipticCurve Λ N ℂ → Submodule ℤ (Fin 2 → ℂ))
      (e : ∀ E : FakeEllipticCurve Λ N ℂ,
        SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)),

      (∀ E : FakeEllipticCurve Λ N ℂ,
        (∃ b₀ : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), latt E = Submodule.span ℤ (Set.range b₀)) ∧
        (∀ x ∈ Λ, ∀ v ∈ latt E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ latt E)) ∧

      (∀ (E : FakeEllipticCurve Λ N ℂ) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f),
        e E (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e E P + e E Q) ∧

      (∀ (E : FakeEllipticCurve Λ N ℂ) (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
        e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
        e E (pushPt (E.act x) (E.act_over x) P) =
          ((((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) ∧

      (∀ (E E' : FakeEllipticCurve Λ N ℂ) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
          mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
        (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) →
        ∃ c : ℂ, (∀ v ∈ latt E, c • v ∈ latt E') ∧
          ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
            e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
            e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup)) ∧

      (∀ (E E' : FakeEllipticCurve Λ N ℂ) (c : ℂ), (∀ v ∈ latt E, c • v ∈ latt E') →
        ∃ (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
            mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
          (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧
          ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
            e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
            e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup)) ∧

      (∀ (E E' : FakeEllipticCurve Λ N ℂ) (φ ψ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (hψ : ψ ≫ E'.f = E.f),
        (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f, mapPt φ hφ P = mapPt ψ hψ P) → φ = ψ) ∧

      (∀ (E : FakeEllipticCurve Λ N ℂ) (U : E.A.Opens) (f : Γ(E.A, U)),
        IsOpen {v : Fin 2 → ℂ | ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∃ F : (Fin 2 → ℂ) → ℂ,
          DifferentiableOn ℂ F {v : Fin 2 → ℂ | ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U} ∧
          ∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U),
            F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
              ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f)) ∧

      (∀ (E : FakeEllipticCurve Λ N ℂ) (v₀ : Fin 2 → ℂ),
        ∃ (U : E.A.Opens) (f₁ f₂ : Γ(E.A, U)) (ε : ℝ) (D : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ))
          (F : (Fin 2 → ℂ) → (Fin 2 → ℂ)),
          0 < ε ∧
          (∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U) ∧
          (∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U),
            v ∈ Metric.ball v₀ ε →
            F v = ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                      ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f₁),
                    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                      ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f₂)]) ∧
          HasFDerivAt F (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v₀) := by sorry
