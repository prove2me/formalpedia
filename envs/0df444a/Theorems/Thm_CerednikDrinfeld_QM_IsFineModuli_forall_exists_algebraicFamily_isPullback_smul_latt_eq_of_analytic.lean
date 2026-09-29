-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_forall_exists_algebraicFamily_isPullback_smul_latt_eq_of_analytic
-- name    : CerednikDrinfeld.QM.IsFineModuli.forall_exists_algebraicFamily_isPullback_smul_latt_eq_of_analytic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/131c3e2d-5ad9-5f85-b699-f5c3c7d9ba70
-- title:
--   Fake elliptic curves near a period lie in one algebraic family
-- statement:
--   Fix primes $q \ne q'$ and $a,b \in \mathbb{Q}$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, its completion at $v$ is a division algebra exactly when $v$ contains $q$ or $q'$; let $\Lambda$ be an order maximal among orders, $\iota$ an injective $\mathbb{Q}$-algebra map into $M_2(\mathbb{R})$, $N \neq 0$ squarefree and prime to $q,q'$, and $R \le \Lambda$ an intersection $\Lambda_1 \cap \Lambda_2$ of two maximal orders of relative index $N$ in $\Lambda_1$. Assume the analytic dictionary for fake elliptic curves of level $N$ over $\mathbb{C}$: a lattice $\mathrm{latt}\,E$ and a bijection $e$ of the $\mathbb{C}$-sections of $E$ with $(\mathbb{C}^2)/\mathrm{latt}\,E$, where $\mathrm{latt}\,E$ is the $\mathbb{Z}$-span of an $\mathbb{R}$-basis of $\mathbb{C}^2$ stable under $\iota(\Lambda)$; $e$ is additive for the group law and intertwines the $\Lambda$-action with matrix multiplication by $\iota(x)_{\mathbb{C}}$; homomorphisms respecting group law and $\Lambda$-action correspond exactly to scalars $c$ with $c \cdot \mathrm{latt}\,E \subseteq \mathrm{latt}\,E'$, and are determined by their effect on $\mathbb{C}$-points; sections of the structure sheaf pull back to holomorphic functions of the uniformising variable, and near each $v_0$ two sections give a map $\mathbb{C}^2 \to \mathbb{C}^2$ with invertible derivative at $v_0$. Assume further $m \ge 3$ prime to $Nqq'$ and a fine moduli scheme $M \to \operatorname{Spec}\mathbb{C}$, via $\mathrm{ptF}$, for fake elliptic curves with full level-$m$ structure, smooth of relative dimension $1$ and proper. Then for every $\tau_0$ in the upper half-plane there are a finite-type $\mathbb{C}$-algebra $S$ that is a domain, a fake elliptic curve $\mathcal{A}$ of level $N$ over $S$, and an open $W \ni \tau_0$, such that every $\tau \in W$ admits $E'$ over $\mathbb{C}$ and $\sigma : S \to \mathbb{C}$ over $\mathbb{C}$ with $E'$ the pullback of $\mathcal{A}$ along $\sigma$, together with $c \ne 0$ satisfying $c \cdot \mathrm{latt}\,E' = \iota(\Lambda)_{\mathbb{C}}\binom{\tau}{1}$, and such that, for $\lambda \in \Lambda$ and $r \in R$, whenever $N^{-1}\iota(\lambda)_{\mathbb{C}}\binom{\tau}{1}$ is $c$ times the $e$-value of a point factoring through the level structure of $E'$, the same holds for $\lambda r$.
--
--   This is the local statement that, in a neighbourhood of any point of the upper half-plane, the fake elliptic curves whose period lattice is the one attached to $\tau$ with $R$-compatible level structure all arise as fibres of a single family over an integral affine base; no quotient by a Fuchsian group or global period map is used. It is what the proof of integrality of the coarse moduli scheme over $\mathbb{C}$, [`CerednikDrinfeld.QM.IsCoarseModuli.isIntegral_of_complex_of_squarefree`](thm.html#CerednikDrinfeld.QM.IsCoarseModuli.isIntegral_of_complex_of_squarefree), needs in order to connect moduli points coming from nearby periods.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_forall_exists_algebraicFamily_isPullback_smul_latt_eq_of_analytic.lean

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

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open AlgebraicCurve
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise

theorem CerednikDrinfeld.QM.IsFineModuli.forall_exists_algebraicFamily_isPullback_smul_latt_eq_of_analytic
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

    (m : ℕ) (hm : 3 ≤ m) (hmc : m.Coprime (N * q * q'))
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of ℂ))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of ℂ)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM)
    (hM : IsFineModuli Λ N m M πM ptF) (hsm : SmoothOfRelativeDimension 1 πM)
    (hprop : IsProper πM) :
    ∀ τ₀ : UpperHalfPlane,
      ∃ (S : Type) (_ : CommRing S) (_ : IsDomain S) (_ : Algebra ℂ S) (_ : Algebra.FiniteType ℂ S)
        (𝒜 : FakeEllipticCurve Λ N S) (W : Set UpperHalfPlane),
        IsOpen W ∧ τ₀ ∈ W ∧
        ∀ τ ∈ W, ∃ (E' : FakeEllipticCurve Λ N ℂ) (σ : S →ₐ[ℂ] ℂ),
          FakeEllipticCurve.IsPullback σ.toRingHom 𝒜 E' ∧
          ∃ c : ℂ, c ≠ 0 ∧ c • latt E' = qmPeriodLattice ι Λ τ ∧
            ∀ (lam : ℍ[ℚ, a, b]), lam ∈ Λ → ∀ r ∈ R,
              (∃ v : Fin 2 → ℂ,
                (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E'.f,
                  FactorsThrough E'.lev P ∧ e E' P = (v : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup)) ∧
                c • v = ((N : ℂ)⁻¹) • qmPeriodMap ι τ lam) →
              (∃ v : Fin 2 → ℂ,
                (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E'.f,
                  FactorsThrough E'.lev P ∧ e E' P = (v : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup)) ∧
                c • v = ((N : ℂ)⁻¹) • qmPeriodMap ι τ (lam * r)) := by sorry
