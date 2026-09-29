-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_forall_exists_algebraicChart_of_periodMap_of_analytic
-- name    : CerednikDrinfeld.QM.IsFineModuli.forall_exists_algebraicChart_of_periodMap_of_analytic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/7c7a2398-06d0-51b8-83e5-c3275eb10b9f
-- title:
--   Local algebraic charts for the quaternionic period map
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0 < a$ or $0 < b$) and, at each finite place $v$ of $\mathbb{Q}$, its completion is a division algebra exactly when $v$ lies above $q$ or $q'$; let $\Lambda$ be a maximal order (an order containing no strictly larger order), $\iota : \mathbb{H}[\mathbb{Q},a,b] \to M_2(\mathbb{R})$ an injective $\mathbb{Q}$-algebra map, $N \geq 1$ squarefree with $q \nmid N$, $q' \nmid N$, and $R \leq \Lambda$ an Eichler order of level $N$, i.e. an intersection of two maximal orders of relative index $N$ in one of them. Let $Fc_0$ be a field which is a curve over $\mathbb{C}$ in the sense of [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15) (principal divisors, finite residue fields at all places, and $\Omega_{Fc_0/\mathbb{C}}$ free of rank one) and essentially of finite type over $\mathbb{C}$, and let $U_0$ be a [`ModularCurve.UniformizedHeckeCurve`](def/ModularCurve_UniformizedHeckeCurve.html#L14) structure on $Fc_0$ for the Fuchsian group `fuchsianGroup R ι` (the norm-one image of the unit group of $R$), so in particular $U_0.\mathrm{pt} : \mathfrak{H} \to$ places of $Fc_0$ identifies exactly the orbits of that group. Further data are an analytic dictionary for fake elliptic curves over $\mathbb{C}$ for $(\Lambda,N)$: a lattice assignment `latt`, bijections $e_E$ between the sections of $E$ over $\mathrm{Spec}\,\mathbb{C}$ and $(\mathbb{C}^2)/\mathrm{latt}(E)$, and hypotheses stating that each $\mathrm{latt}(E)$ is spanned over $\mathbb{Z}$ by an $\mathbb{R}$-basis of $\mathbb{C}^2$ and is stable under $\Lambda$ acting through $\iota$, that $e_E$ is additive for the relative group law and equivariant for the $\Lambda$-action by `mulVec`, that morphisms of families commuting with group law and $\Lambda$-action correspond exactly to scalars $c \in \mathbb{C}$ with $c \cdot \mathrm{latt}(E) \subseteq \mathrm{latt}(E')$ and are determined by their effect on $\mathbb{C}$-points, and that reading off sections of the structure sheaf along $e_E^{-1}$ gives holomorphic functions, with two sections providing a local chart with invertible derivative at each point (these analytic hypotheses are summarised here). Finally fix $m \geq 3$ coprime to $N q q'$, a scheme $M$ with $\pi_M : M \to \mathrm{Spec}\,\mathbb{C}$ and a point functor $\mathrm{ptF}$ making $(M,\pi_M,\mathrm{ptF})$ a fine moduli scheme for fake elliptic curves with full level $m$ structure, with $\pi_M$ smooth of relative dimension one and proper, and a map $\mathrm{perE}$ from fake elliptic curves over $\mathbb{C}$ to $\mathfrak{H}$ such that $U_0.\mathrm{pt}(\mathrm{perE}\,E) = U_0.\mathrm{pt}(\tau)$ holds precisely when some $c \neq 0$ satisfies $c \cdot \mathrm{latt}(E) = \mathrm{qmPeriodLattice}\,\iota\,\Lambda\,\tau$ and, for all $\lambda \in \Lambda$ and $r \in R$, whenever $N^{-1}$ times the period of $\lambda$ is $c \cdot v$ for some $v$ representing a point of $E$ factoring through the level structure $E.\mathrm{lev}$, the same holds for $\lambda r$. The conclusion: for every $\tau_0 \in \mathfrak{H}$ there are a finite-type $\mathbb{C}$-algebra $S$ which is a domain, a fake elliptic curve $\mathcal{A}$ over $S$ for $(\Lambda,N)$, an open set $W \subseteq \mathfrak{H}$ containing $\tau_0$, and a map $h : \mathfrak{H} \to (S \to_{\mathbb{C}\text{-alg}} \mathbb{C})$ injective on $W$, such that for every $s \in S$ the function $\tau \mapsto h(\tau)(s)$ is the restriction of a function holomorphic on $\{z : \mathrm{Im}\,z > 0,\ z \in W\}$, and such that for every $\tau \in W$ and every fake elliptic curve $E'$ over $\mathbb{C}$ obtained as the pullback of $\mathcal{A}$ along $h(\tau)$ one has $U_0.\mathrm{pt}(\mathrm{perE}\,E') = U_0.\mathrm{pt}(\tau)$.
--
--   This provides the local algebraic charts on the quaternionic Shimura curve: near each point of the upper half-plane the period map is realised by an affine algebraic family $\mathcal{A}/S$ together with a holomorphic family of $\mathbb{C}$-points of $S$, so that pulling back $\mathcal{A}$ recovers the fake elliptic curves with period $\tau$. It is the input to [`CerednikDrinfeld.QM.exists_periodMap_meromorphicRealization_of_uniformizedHeckeCurve_of_two_mul_dvd`](thm.html#CerednikDrinfeld.QM.exists_periodMap_meromorphicRealization_of_uniformizedHeckeCurve_of_two_mul_dvd), where these charts are used to produce meromorphic realisations of functions on the uniformised Hecke curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_forall_exists_algebraicChart_of_periodMap_of_analytic.lean

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

theorem CerednikDrinfeld.QM.IsFineModuli.forall_exists_algebraicChart_of_periodMap_of_analytic
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (hqq' : q' ≠ q)
    {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)

    (Fc₀ : Type) [Field Fc₀] [Algebra ℂ Fc₀] [AlgebraicCurve.IsCurveOver ℂ Fc₀] [Algebra.EssFiniteType ℂ Fc₀]
    (U₀ : ModularCurve.UniformizedHeckeCurve (fuchsianGroup R ι) Fc₀)

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
    (hprop : IsProper πM)

    (perE : FakeEllipticCurve Λ N ℂ → UpperHalfPlane)
    (hperE : ∀ (E : FakeEllipticCurve Λ N ℂ) (τ : UpperHalfPlane),
      U₀.pt (perE E) = U₀.pt τ ↔
        ∃ c : ℂ, c ≠ 0 ∧ c • latt E = qmPeriodLattice ι Λ τ ∧
          ∀ (lam : ℍ[ℚ, a, b]), lam ∈ Λ → ∀ r ∈ R,
            (∃ v : Fin 2 → ℂ,
              (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
                FactorsThrough E.lev P ∧ e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) ∧
              c • v = ((N : ℂ)⁻¹) • qmPeriodMap ι τ lam) →
            (∃ v : Fin 2 → ℂ,
              (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
                FactorsThrough E.lev P ∧ e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) ∧
              c • v = ((N : ℂ)⁻¹) • qmPeriodMap ι τ (lam * r))) :
    ∀ τ₀ : UpperHalfPlane,
      ∃ (S : Type) (_ : CommRing S) (_ : IsDomain S) (_ : Algebra ℂ S) (_ : Algebra.FiniteType ℂ S)
        (𝒜 : FakeEllipticCurve Λ N S) (W : Set UpperHalfPlane) (h : UpperHalfPlane → (S →ₐ[ℂ] ℂ)),
        IsOpen W ∧ τ₀ ∈ W ∧ Set.InjOn h W ∧
        (∀ s : S, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {z : ℂ | 0 < z.im ∧ UpperHalfPlane.ofComplex z ∈ W} ∧
          ∀ z : ℂ, 0 < z.im → UpperHalfPlane.ofComplex z ∈ W → F z = h (UpperHalfPlane.ofComplex z) s) ∧
        (∀ τ ∈ W, ∀ E' : FakeEllipticCurve Λ N ℂ,
          FakeEllipticCurve.IsPullback (h τ).toRingHom 𝒜 E' → U₀.pt (perE E') = U₀.pt τ) := by sorry
