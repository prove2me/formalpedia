-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_isOpen_injOn_periodChart_fullLevel_of_analytic_of_isEichlerOrder
-- name    : CerednikDrinfeld.QM.IsFineModuli.exists_isOpen_injOn_periodChart_fullLevel_of_analytic_of_isEichlerOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/efce7f4c-ef60-5bfa-93aa-1964d9e66e80
-- title:
--   Local period chart on the fine moduli curve with full level
-- statement:
--   Fix primes $q \neq q'$ and $a, b \in \mathbb{Q}$ such that $0 < a$ or $0 < b$ and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, the completion $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$; let $\Lambda$ be a maximal order (an order containing no strictly larger order), $\iota$ an injective $\mathbb{Q}$-algebra map $\mathbb{H}[\mathbb{Q},a,b] \to M_2(\mathbb{R})$, $N \neq 0$ squarefree and prime to $q$ and $q'$, and $R \leq \Lambda$ an Eichler order of level $N$, i.e. an intersection $\Lambda_1 \cap \Lambda_2$ of maximal orders of relative index $N$ in $\Lambda_1$. Assume given the analytic dictionary for fake elliptic curves over $\mathbb{C}$ with $\Lambda$-action and level $N$: a lattice $\mathrm{latt}(E) \subseteq \mathbb{C}^2$ and a bijection $e_E$ from the sections of $E.f$ over $\mathrm{Spec}\,\mathbb{C}$ to $\mathbb{C}^2/\mathrm{latt}(E)$, subject to: $\mathrm{latt}(E)$ is spanned over $\mathbb{Z}$ by an $\mathbb{R}$-basis of $\mathbb{C}^2$ and is stable under $\iota(\Lambda)$ acting by `mulVec`; $e_E$ is additive for the relative group law and intertwines the action of $x \in \Lambda$ with multiplication by $\iota(x)$; every morphism $E.A \to E'.A$ over $\mathbb{C}$ compatible with the group laws and the $\Lambda$-actions is given by a scalar $c$ with $c \cdot \mathrm{latt}(E) \subseteq \mathrm{latt}(E')$, conversely every such scalar comes from such a morphism, and morphisms are determined by their effect on $\mathbb{C}$-points; and two analyticity clauses, namely that for each open $U \subseteq E.A$ and $f \in \Gamma(E.A,U)$ the locus of $v \in \mathbb{C}^2$ whose point lands in $U$ is open and $v \mapsto f$ evaluated there is holomorphic on it, and that near each $v_0$ two sections give a map $F$ to $\mathbb{C}^2$ with an invertible derivative at $v_0$. Let $m \geq 3$, let $\pi_M : M \to \mathrm{Spec}\,\mathbb{C}$ be smooth of relative dimension $1$, and let $\mathrm{ptF}$, assigning to each ring $S$, each $S$-point $s$ and each fake elliptic curve over $S$ with full level-$m$ structure a point of $M$ over $s$, satisfy `IsFineModuli`: invariance under isomorphism, compatibility with base change, surjectivity onto points over each $s$, and injectivity up to isomorphism. Then for every $\mathbb{C}$-point $\sigma_0$ of $M$ there are an open $W \subseteq \mathfrak{H}$ and a map $h$ from $\mathfrak{H}$ to $\mathbb{C}$-points of $M$ with $\sigma_0 \in h(W)$, injective on $W$, holomorphic in the sense that for every open $U \subseteq M$ and $s \in \Gamma(M,U)$ the set of $z$ with $\mathrm{Im}\,z > 0$, $z \in W$ and $h(z)$ factoring through $U$ is open and $z \mapsto s(h(z))$ agrees there with a function holomorphic on it, and there is a single $x_0 \in \Lambda$ such that for every $\tau \in W$ and every fake elliptic curve with full level $u = (E, P)$ over $\mathbb{C}$ classified by $h(\tau)$ there is $c \neq 0$ with $c \cdot \mathrm{latt}(E) = \iota(\Lambda)\binom{\tau}{1}$, with the set of $\lambda \in \Lambda$ for which $N^{-1}\iota(\lambda)\binom{\tau}{1}$ lies in $c$ times the image under $e_E$ of the points factoring through $E.\mathrm{lev}$ stable under right multiplication by $R$, and with $c \cdot e_E(P) = m^{-1}\iota(x_0)\binom{\tau}{1}$ for some representative of $e_E(P)$.
--
--   This is the complex-analytic uniformisation of a fine moduli scheme of fake elliptic curves with $\Lambda$-action, level $N$ and full level $m$: locally the moduli curve is parametrised by the upper half-plane via the period lattices $\iota(\Lambda)\binom{\tau}{1}$, with the Eichler level structure recorded as right $R$-stability of an associated $\Lambda$-submodule and the full level-$m$ point given by a fixed $x_0 \in \Lambda$ independently of $\tau$. It feeds the construction of local algebraic families of fake elliptic curves carrying an extra level structure at a prime dividing $N$, used in identifying Shimura curves over $\mathbb{Q}$ with quaternionic quotients of $\mathfrak{H}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_exists_isOpen_injOn_periodChart_fullLevel_of_analytic_of_isEichlerOrder.lean

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
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise

theorem CerednikDrinfeld.QM.IsFineModuli.exists_isOpen_injOn_periodChart_fullLevel_of_analytic_of_isEichlerOrder
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

    (m : ℕ) (hm : 3 ≤ m)
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of ℂ))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of ℂ)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM)
    (hM : IsFineModuli Λ N m M πM ptF) (hsm : SmoothOfRelativeDimension 1 πM)
    (σ₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) πM) :
    ∃ (W : Set UpperHalfPlane) (_ : IsOpen W) (h : UpperHalfPlane → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) πM),
      σ₀ ∈ h '' W ∧ Set.InjOn h W ∧

      (∀ (U : M.Opens) (s : Γ(M, U)),
        IsOpen {z : ℂ | 0 < z.im ∧ UpperHalfPlane.ofComplex z ∈ W ∧ ⊤ ≤ (h (UpperHalfPlane.ofComplex z)).1 ⁻¹ᵁ U} ∧
        ∃ F : ℂ → ℂ,
        DifferentiableOn ℂ F
          {z : ℂ | 0 < z.im ∧ UpperHalfPlane.ofComplex z ∈ W ∧ ⊤ ≤ (h (UpperHalfPlane.ofComplex z)).1 ⁻¹ᵁ U} ∧
        ∀ (z : ℂ), 0 < z.im → UpperHalfPlane.ofComplex z ∈ W →
          ∀ hU : ⊤ ≤ (h (UpperHalfPlane.ofComplex z)).1 ⁻¹ᵁ U,
            F z = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((h (UpperHalfPlane.ofComplex z)).1.appLE U ⊤ hU) s)) ∧

      (∃ x₀ : ℍ[ℚ, a, b], x₀ ∈ Λ ∧
        (∀ τ ∈ W, ∀ u : FakeEllipticCurve.WithFullLevel Λ N m ℂ,
          ptF ℂ (𝟙 (Spec (CommRingCat.of ℂ))) u = h τ →
          ∃ c : ℂ, c ≠ 0 ∧ c • latt u.1 = qmPeriodLattice ι Λ τ ∧

            (∀ (lam : ℍ[ℚ, a, b]), lam ∈ Λ → ∀ r ∈ R,
              (∃ v : Fin 2 → ℂ,
                (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) u.1.f,
                  FactorsThrough u.1.lev P ∧ e u.1 P = (v : (Fin 2 → ℂ) ⧸ (latt u.1).toAddSubgroup)) ∧
                c • v = ((N : ℂ)⁻¹) • qmPeriodMap ι τ lam) →
              (∃ v : Fin 2 → ℂ,
                (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) u.1.f,
                  FactorsThrough u.1.lev P ∧ e u.1 P = (v : (Fin 2 → ℂ) ⧸ (latt u.1).toAddSubgroup)) ∧
                c • v = ((N : ℂ)⁻¹) • qmPeriodMap ι τ (lam * r))) ∧

            (∃ v : Fin 2 → ℂ,
              e u.1 u.2.P = (v : (Fin 2 → ℂ) ⧸ (latt u.1).toAddSubgroup) ∧
              c • v = ((m : ℂ)⁻¹) • qmPeriodMap ι τ x₀))) := by sorry
