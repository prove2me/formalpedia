-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_WithFullLevel_iso_of_smul_latt_subset_of_level_iff_of_generator
-- name    : CerednikDrinfeld.QM.WithFullLevel.iso_of_smul_latt_subset_of_level_iff_of_generator
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/329cffc7-4ad8-5481-bd89-caa40ed6923f
-- title:
--   Isomorphism of full-level fake elliptic curves from a homothety
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ with `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $a>0$ or $b>0$ and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$; a maximal order $\Lambda$ (an order maximal among orders containing it), an injective $\mathbb{Q}$-algebra map $\iota : \mathbb{H}[\mathbb{Q},a,b] \to M_2(\mathbb{R})$, a nonzero squarefree $N$ prime to $q$ and $q'$, and a submodule $R \le \Lambda$ which is an intersection of two maximal orders of relative index $N$ in the first. Assume the analytic dictionary over $\mathbb{C}$: an assignment $E \mapsto \mathrm{latt}(E)$ of a $\mathbb{Z}$-submodule of $\mathbb{C}^2$ to each fake elliptic curve $E$ of level $N$ with $\Lambda$-action over $\mathbb{C}$, and bijections $e_E$ from the $\mathbb{C}$-points of $E$ (sections of $E.f$ over $\mathrm{id}_{\operatorname{Spec}\mathbb{C}}$) to $\mathbb{C}^2/\mathrm{latt}(E)$, together with: $\mathrm{latt}(E)$ is spanned over $\mathbb{Z}$ by an $\mathbb{R}$-basis of $\mathbb{C}^2$ and stable under $\iota(\Lambda)$ acting by matrix multiplication (hL1); $e_E$ is additive for the relative group law (hE1) and turns the action of $x \in \Lambda$ into multiplication by $\iota(x)$ (hE2); every morphism $\varphi : E \to E'$ over $\mathbb{C}$ that is a homomorphism on $T$-valued points for all $T$ and commutes with the $\Lambda$-actions is given on $\mathbb{C}$-points by some scalar $c$ with $c\,\mathrm{latt}(E) \subseteq \mathrm{latt}(E')$ (hH1), conversely every such scalar is realised by such a $\varphi$ (hH2), and a morphism over $\mathbb{C}$ is determined by its effect on $\mathbb{C}$-points (hH3); finally the analyticity hypotheses (hAN) that pullbacks of sections along $e_E^{-1}$ are holomorphic on open loci, and (hCOV) that near each point of $\mathbb{C}^2$ two sections give a chart with invertible derivative. Let $m \in \mathbb{N}$ and let $uu = (E,\xi)$, $uu' = (E',\xi')$ be fake elliptic curves of level $N$ over $\mathbb{C}$ equipped with full level-$m$ structures. Let $H \neq 0$ in $\mathbb{C}$ satisfy $H\,\mathrm{latt}(E) \subseteq \mathrm{latt}(E')$ and $H^{-1}\mathrm{latt}(E') \subseteq \mathrm{latt}(E)$, assume that for every $w \in \mathbb{C}^2$ there is a $\mathbb{C}$-point of $E$ factoring through $E.\mathrm{lev}$ with $e_E$-image $[w]$ if and only if there is a $\mathbb{C}$-point of $E'$ factoring through $E'.\mathrm{lev}$ with $e_{E'}$-image $[Hw]$, and assume $e_{E'}(\xi'.P) = [Hw_0]$ whenever $e_E(\xi.P) = [w_0]$. Then $uu$ and $uu'$ are isomorphic as objects with full level structure: there is an isomorphism of schemes $E.A \cong E'.A$ compatible with the structure morphisms to $\operatorname{Spec}\mathbb{C}$, which is a homomorphism for the relative group laws on $T$-valued points for every $T$, commutes with the actions of all $x \in \Lambda$, matches the level-$N$ conditions (a $T$-valued point factors through $E.\mathrm{lev}$ iff its image factors through $E'.\mathrm{lev}$), and carries $\xi.P$ to $\xi'.P$.
--
--   This is the scheme-theoretic half of the injectivity statement for the period map on the moduli of fake elliptic curves with full level structure: a homothety of the period lattices respecting the level-$N$ points and the level-$m$ generator comes from an isomorphism of the moduli data. It is used by [`CerednikDrinfeld.QM.IsFineModuli.injOn_periodFunction_of_latticeFrame_of_analytic`](thm.html#CerednikDrinfeld.QM.IsFineModuli.injOn_periodFunction_of_latticeFrame_of_analytic) and its variant without the coprimality assumption.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_WithFullLevel_iso_of_smul_latt_subset_of_level_iff_of_generator.lean

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
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise BigOperators

theorem CerednikDrinfeld.QM.WithFullLevel.iso_of_smul_latt_subset_of_level_iff_of_generator
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (hqq' : q' ≠ q)
    {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)

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

    (hAN : ∀ (E : FakeEllipticCurve Λ N ℂ) (U : E.A.Opens) (f : Γ(E.A, U)),
        IsOpen {v : Fin 2 → ℂ | ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∃ F : (Fin 2 → ℂ) → ℂ,
          DifferentiableOn ℂ F {v : Fin 2 → ℂ | ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U} ∧
          ∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U),
            F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
              ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f))

    (hCOV : ∀ (E : FakeEllipticCurve Λ N ℂ) (v₀ : Fin 2 → ℂ),
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
          HasFDerivAt F (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v₀)
    (m : ℕ)
    (uu uu' : FakeEllipticCurve.WithFullLevel Λ N m ℂ) (H : ℂ) (hH : H ≠ 0)
    (hL : ∀ w ∈ latt uu.1, H • w ∈ latt uu'.1)
    (hL' : ∀ w ∈ latt uu'.1, H⁻¹ • w ∈ latt uu.1)
    (hlev : ∀ w : Fin 2 → ℂ,
      (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) uu.1.f,
          FactorsThrough uu.1.lev P ∧ e uu.1 P = ((w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt uu.1).toAddSubgroup)) ↔
      (∃ P' : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) uu'.1.f,
          FactorsThrough uu'.1.lev P' ∧ e uu'.1 P' = ((H • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt uu'.1).toAddSubgroup)))
    (hgen : ∀ w₀ : Fin 2 → ℂ, e uu.1 uu.2.P = ((w₀ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt uu.1).toAddSubgroup) →
      e uu'.1 uu'.2.P = ((H • w₀ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt uu'.1).toAddSubgroup)) :
    FakeEllipticCurve.WithFullLevel.Iso uu uu' := by sorry
