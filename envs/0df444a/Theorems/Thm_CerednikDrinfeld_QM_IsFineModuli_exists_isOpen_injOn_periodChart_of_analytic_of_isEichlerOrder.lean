-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_isOpen_injOn_periodChart_of_analytic_of_isEichlerOrder
-- name    : CerednikDrinfeld.QM.IsFineModuli.exists_isOpen_injOn_periodChart_of_analytic_of_isEichlerOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/221a5fb5-8b2f-5d5e-aae0-51eeebb2ff5a
-- title:
--   Local period chart near a point of the fine moduli curve
-- statement:
--   Fix primes $q \ne q'$ and $a,b \in \mathbb{Q}$ with `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $a>0$ or $b>0$ and, for every finite place $v$ of $\mathbb{Q}$, the algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra exactly when $v$ lies over $q$ or $q'$. Let $\Lambda$ be a maximal order (an order maximal among orders containing it), $\iota$ an injective $\mathbb{Q}$-algebra map $\mathbb{H}[\mathbb{Q},a,b] \to M_2(\mathbb{R})$, $N \neq 0$ squarefree and prime to $q,q'$, and $R \subseteq \Lambda$ an Eichler order of level $N$, i.e. an intersection of two maximal orders of relative index $N$. Further data: a lattice assignment `latt` sending each fake elliptic curve $E$ over $\mathbb{C}$ with $\Lambda$-action and level-$N$ structure to a $\mathbb{Z}$-submodule of $\mathbb{C}^2$, and bijections $e_E$ from the $\mathbb{C}$-points of $E$ to $\mathbb{C}^2/\mathrm{latt}(E)$; the hypotheses assert that $\mathrm{latt}(E)$ is spanned by an $\mathbb{R}$-basis of $\mathbb{C}^2$ and stable under $\iota(\Lambda)$ acting by complexified matrices, that $e_E$ is additive for the relative group law and intertwines the $\Lambda$-action with that matrix action, that morphisms over $\mathbb{C}$ respecting the group law and the $\Lambda$-action correspond exactly to scalars $c$ with $c \cdot \mathrm{latt}(E) \subseteq \mathrm{latt}(E')$ and are determined by their effect on $\mathbb{C}$-points, and that sections of the structure sheaf become holomorphic functions of the uniformising parameter $v \in \mathbb{C}^2$, with pairs of sections providing local charts with invertible derivative (summarised here). Finally let $m \ge 3$ be coprime to $Nqq'$, let $\pi_M : M \to \mathrm{Spec}\,\mathbb{C}$ be smooth of relative dimension $1$ together with $\mathrm{ptF}$ making $(M,\pi_M,\mathrm{ptF})$ a fine moduli scheme for fake elliptic curves with full level-$m$ structure (classifying maps constant on isomorphism classes, compatible with base change along ring maps, surjective and injective on isomorphism classes), and let $\sigma_0$ be a $\mathbb{C}$-point of $M$. The conclusion: there are an open $W \subseteq \mathfrak{H}$ and a map $h$ from $\mathfrak{H}$ to the $\mathbb{C}$-points of $M$ with $\sigma_0 \in h(W)$, $h$ injective on $W$, such that (i) for every open $U \subseteq M$ and every $s \in \Gamma(M,U)$ the set of $z$ with $\mathrm{Im}\,z>0$, $z \in W$ and $h(z)$ landing in $U$ is open, and the value of $s$ at $h(z)$ is given on it by a function holomorphic there; and (ii) for every $\tau \in W$ and every fake elliptic curve with full level-$m$ structure $u$ over $\mathbb{C}$ classified by $h(\tau)$, there is $c \neq 0$ with $c \cdot \mathrm{latt}(u)$ equal to the period lattice $\mathrm{qmPeriodLattice}\,\iota\,\Lambda\,\tau$, the image of $\Lambda$ under $x \mapsto \iota(x)_{\mathbb{C}} \cdot (\tau,1)^{t}$, and moreover the set of $\lambda \in \Lambda$ for which $N^{-1} \cdot \mathrm{qmPeriodMap}\,\iota\,\tau\,\lambda$ is, after scaling by $c$, represented by a point of $u$ factoring through its level-$N$ structure is stable under right multiplication by elements of $R$.
--
--   This is the local uniformisation (period chart) step for the Shimura curve attached to an indefinite quaternion algebra ramified exactly at $q$ and $q'$: near any complex point of the fine moduli scheme at full level $m$ the classifying map is parametrised injectively and holomorphically by an open subset of the upper half-plane, the fibre over $\tau$ having period lattice the image of $\Lambda$ under $\tau$ and its level-$N$ structure the one singled out by the Eichler order $R$. It is used downstream to produce algebraic charts and algebraic families with prescribed period lattices, and to show that the locus of points whose lattice is a quaternionic period lattice is closed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_exists_isOpen_injOn_periodChart_of_analytic_of_isEichlerOrder.lean

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

theorem CerednikDrinfeld.QM.IsFineModuli.exists_isOpen_injOn_periodChart_of_analytic_of_isEichlerOrder
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

      (∀ τ ∈ W, ∀ u : FakeEllipticCurve.WithFullLevel Λ N m ℂ,
        ptF ℂ (𝟙 (Spec (CommRingCat.of ℂ))) u = h τ →
        ∃ c : ℂ, c ≠ 0 ∧ c • latt u.1 = qmPeriodLattice ι Λ τ ∧

          ∀ (lam : ℍ[ℚ, a, b]), lam ∈ Λ → ∀ r ∈ R,
            (∃ v : Fin 2 → ℂ,
              (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) u.1.f,
                FactorsThrough u.1.lev P ∧ e u.1 P = (v : (Fin 2 → ℂ) ⧸ (latt u.1).toAddSubgroup)) ∧
              c • v = ((N : ℂ)⁻¹) • qmPeriodMap ι τ lam) →
            (∃ v : Fin 2 → ℂ,
              (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) u.1.f,
                FactorsThrough u.1.lev P ∧ e u.1 P = (v : (Fin 2 → ℂ) ⧸ (latt u.1).toAddSubgroup)) ∧
              c • v = ((N : ℂ)⁻¹) • qmPeriodMap ι τ (lam * r))) := by sorry
