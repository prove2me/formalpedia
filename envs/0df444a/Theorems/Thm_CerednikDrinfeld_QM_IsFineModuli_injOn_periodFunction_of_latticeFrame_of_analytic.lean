-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_injOn_periodFunction_of_latticeFrame_of_analytic
-- name    : CerednikDrinfeld.QM.IsFineModuli.injOn_periodFunction_of_latticeFrame_of_analytic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/46c420c1-cae6-5321-ad88-5d53e32f8777
-- title:
--   Injectivity of τ on an analytic lattice-frame chart
-- statement:
--   Let $q,q'$ be distinct primes and $a,b\in\mathbb Q$ with $\mathbb H[\mathbb Q,a,b]$ indefinite ($0<a$ or $0<b$) and division at exactly those finite places containing $q$ or $q'$; let $\Lambda$ be a maximal order, $\iota:\mathbb H[\mathbb Q,a,b]\to M_2(\mathbb R)$ an injective $\mathbb Q$-algebra map, $N\neq 0$ squarefree with $q\nmid N$, $q'\nmid N$, and $R\le\Lambda$ an Eichler order, i.e. an intersection of two maximal orders of relative index $N$. Assume a fibrewise uniformisation dictionary for fake elliptic curves over $\mathbb C$ with $\Lambda$-action and level-$N$ structure: a lattice $\mathrm{latt}(E)\subset\mathbb C^2$ and a bijection $e_E$ from $\mathbb C$-points of $E$ to $\mathbb C^2/\mathrm{latt}(E)$, with `hL1` (each $\mathrm{latt}(E)$ is spanned over $\mathbb Z$ by an $\mathbb R$-basis and is stable under the complexified matrices $\iota x$, $x\in\Lambda$), `hE1`, `hE2` ($e_E$ additive for the relative group law and equivariant, the action of $x$ becoming multiplication by $\iota x$), `hH1`, `hH2` (group-law preserving $\Lambda$-equivariant morphisms over $\mathbb C$ correspond exactly to scalars $c$ with $c\cdot\mathrm{latt}(E)\subseteq\mathrm{latt}(E')$), `hH3` (such morphisms are determined by their effect on $\mathbb C$-points), and `hAN`, `hCOV` (sections of $E$ pull back to holomorphic functions of the period coordinate, and two sections give a local chart with invertible derivative at each point). Let $m\ge 3$ be coprime to $Nqq'$, let $\pi_M:M\to\operatorname{Spec}\mathbb C$ together with $\mathrm{ptF}$ be a fine moduli scheme for such curves with full level-$m$ structure (the assignment $\mathrm{ptF}$ being isomorphism-invariant, compatible with base change, surjective and injective up to isomorphism), with $\pi_M$ smooth of relative dimension $1$. Let $S_c$ be a finitely generated $\mathbb C$-algebra domain, $j:\operatorname{Spec}S_c\to M$ an open immersion over $\mathbb C$, $t\in S_c$, $\sigma_0$ a $\mathbb C$-point, $r>0$ and $\mathcal U$ a set of $\mathbb C$-algebra maps $S_c\to\mathbb C$ containing $\sigma_0$ such that $\sigma\mapsto\sigma t$ is a bijection of $\mathcal U$ onto the ball $B(\sigma_0 t,r)$ and each $s\in S_c$ becomes a holomorphic function of $\sigma t$ there. Finally, on $D=B(\sigma_0 t,\varepsilon)$ with $0<\varepsilon\le r$, let $u$ assign to each $z$ a curve with full level $m$ whose moduli point is $\sigma$ followed by $j$ for the $\sigma\in\mathcal U$ with $\sigma t=z$, let $\kappa(z)\neq0$, let $v_1(z),\dots,v_4(z)$ be a $\mathbb Z$-basis of $\kappa(z)\cdot\mathrm{latt}(u(z))$, let the points factoring through the level-$N$ structure be exactly the classes $\kappa(z)^{-1}N^{-1}\sum_i n_i v_i(z)$ for $n$ in a fixed set $T$, let the level-$m$ point have period class $\kappa(z)^{-1}m^{-1}\sum_i a_{0,i}v_i(z)$ for a fixed $a_0$, and let $\tau:D\to\mathfrak h$, $c$ nonvanishing on $D$ and $y_1,\dots,y_4\in\mathbb H[\mathbb Q,a,b]$ satisfy $c(z)v_i(z)=(\iota y_i)\binom{\tau(z)}{1}$. Then $z\mapsto\tau(z)$ is injective on $D$.
--
--   This is the injectivity half of the statement that the uniformising coordinate on the upper half-plane is a local analytic parameter for the fine moduli scheme of fake elliptic curves with full level-$m$ structure, in the style of Shimura's description of quaternionic moduli. It feeds the construction of an analytic period chart, [`CerednikDrinfeld.QM.IsFineModuli.exists_isOpen_injOn_periodChart_of_analytic_of_isEichlerOrder`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_isOpen_injOn_periodChart_of_analytic_of_isEichlerOrder), and is proved from the dictionary between homotheties of period lattices and $\Lambda$-equivariant isogenies together with the resulting isomorphism criterion for curves with full level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_injOn_periodFunction_of_latticeFrame_of_analytic.lean

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

theorem CerednikDrinfeld.QM.IsFineModuli.injOn_periodFunction_of_latticeFrame_of_analytic
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

    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (j : Spec (CommRingCat.of Sc) ⟶ M) [IsOpenImmersion j]
    (hj : j ≫ πM = Spec.map (CommRingCat.ofHom (algebraMap ℂ Sc)))
    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ)) (hr : 0 < r) (hσ₀ : σ₀ ∈ 𝒰)
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t))

    (ε : ℝ) (hε : 0 < ε) (hεr : ε ≤ r)
    (u : ℂ → FakeEllipticCurve.WithFullLevel Λ N m ℂ) (κ : ℂ → ℂ) (v : Fin 4 → ℂ → (Fin 2 → ℂ))
    (T : Set (Fin 4 → ℤ)) (a₀ : Fin 4 → ℤ)
    (hκ : ∀ z ∈ Metric.ball (σ₀ t) ε, κ z ≠ 0)
    (hPT : ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₀ t) ε →
        ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) πM,
          x.1 = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ j →
          ptF ℂ (𝟙 (Spec (CommRingCat.of ℂ))) (u (σ t)) = x)
    (hBASIS : ∀ z ∈ Metric.ball (σ₀ t) ε,
        (∀ i : Fin 4, v i z ∈ κ z • latt (u z).1) ∧
        ∀ x ∈ κ z • latt (u z).1, ∃! n : Fin 4 → ℤ, (∑ i, (n i : ℂ) • v i z) = x)
    (hLEVN : ∀ z ∈ Metric.ball (σ₀ t) ε, ∀ w : Fin 2 → ℂ,
        (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u z).1.f,
            FactorsThrough (u z).1.lev P ∧ e (u z).1 P = (w : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup)) ↔
          ∃ n ∈ T, (w : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup) =
            (((κ z)⁻¹ • (((N : ℂ)⁻¹) • ∑ i, (n i : ℂ) • v i z) : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup))
    (hLEVM : ∀ z ∈ Metric.ball (σ₀ t) ε,
        e (u z).1 (u z).2.P =
          (((κ z)⁻¹ • (((m : ℂ)⁻¹) • ∑ i, (a₀ i : ℂ) • v i z) : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup))

    (τ : ℂ → UpperHalfPlane) (c : ℂ → ℂ) (y : Fin 4 → ℍ[ℚ, a, b])
    (hc : ∀ z ∈ Metric.ball (σ₀ t) ε, c z ≠ 0)
    (hper : ∀ z ∈ Metric.ball (σ₀ t) ε, ∀ i : Fin 4, c z • v i z = qmPeriodMap ι (τ z) (y i)) :
    Set.InjOn (fun z : ℂ => τ z) (Metric.ball (σ₀ t) ε) := by sorry
