-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_holomorphic_latticeFrame_of_analytic_of_smooth_algebraicChart_noCoprime
-- name    : CerednikDrinfeld.QM.IsFineModuli.exists_holomorphic_latticeFrame_of_analytic_of_smooth_algebraicChart_noCoprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/020ddcb6-f62b-54c8-a516-b32dc4aa9ad6
-- title:
--   Holomorphic lattice frame over a smooth analytic chart
-- statement:
--   Fix primes $q\neq q'$ and $a,b\in\mathbb{Q}$ with `hB`: $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$. Fix a maximal order $\Lambda$ (an order not properly contained in an order), an injective $\mathbb{Q}$-algebra map $\iota:\mathbb{H}[\mathbb{Q},a,b]\to M_2(\mathbb{R})$, a nonzero squarefree $N$ prime to $q$ and $q'$, and $R\le\Lambda$ an Eichler order of level $N$, i.e. an intersection of two maximal orders of relative index $N$ in the first. Assume given, for each fake elliptic curve $E$ over $\mathbb{C}$ with $\Lambda$-action and level-$N$ structure, a $\mathbb{Z}$-submodule $\mathrm{latt}(E)\subseteq\mathbb{C}^2$ and a bijection $e_E$ from the $\mathbb{C}$-points of $E$ onto $\mathbb{C}^2/\mathrm{latt}(E)$, subject to: `hL1`, $\mathrm{latt}(E)$ is the $\mathbb{Z}$-span of an $\mathbb{R}$-basis of $\mathbb{C}^2$ and is stable under $\iota(x)$ for $x\in\Lambda$; `hE1`, `hE2`, $e_E$ is additive for the relative group law and carries the action of $x\in\Lambda$ to multiplication by $\iota(x)$; `hH1`, `hH2`, morphisms over $\mathbb{C}$ respecting the group law and commuting with $\Lambda$ correspond exactly to scalars $c$ with $c\cdot\mathrm{latt}(E)\subseteq\mathrm{latt}(E')$, compatibly with $e$; `hH3`, such morphisms are determined by their effect on $\mathbb{C}$-points; `hAN`, for every open $U$ and $f\in\Gamma(E.A,U)$ the locus of $v\in\mathbb{C}^2$ whose point lies in $U$ is open and $f$ pulls back to a holomorphic function of $v$ there; `hCOV`, near each $v_0$ two sections give a map to $\mathbb{C}^2$ with invertible derivative at $v_0$. Fix $m\ge 3$ and $\pi_M:M\to\operatorname{Spec}\mathbb{C}$ smooth of relative dimension $1$, together with $\mathrm{ptF}$ making $(M,\pi_M)$ a fine moduli scheme for fake elliptic curves with full level $m$ (isomorphism-invariance, compatibility with pullback of rings, surjectivity on points, and injectivity up to isomorphism). Fix an algebraic chart: a smooth finite-type $\mathbb{C}$-domain $S_c$ with $\operatorname{rank}_{S_c}\Omega_{S_c/\mathbb{C}}=1$, an open immersion $j:\operatorname{Spec}S_c\to M$ over $\mathbb{C}$, an element $t\in S_c$, a $\mathbb{C}$-character $\sigma_0$, $r>0$, and a set $\mathcal{U}$ of characters containing $\sigma_0$ such that $\sigma\mapsto\sigma(t)$ is a bijection of $\mathcal{U}$ onto the ball $B(\sigma_0(t),r)$ and every $s\in S_c$ satisfies $\sigma(s)=F_s(\sigma(t))$ for some $F_s$ holomorphic on that ball. The conclusion asserts the existence of $0<\varepsilon\le r$, a family $z\mapsto u_z$ of fake elliptic curves over $\mathbb{C}$ with full level $m$, a nowhere-vanishing $\kappa$ on $B(\sigma_0(t),\varepsilon)$, four maps $v_1,\dots,v_4:\mathbb{C}\to\mathbb{C}^2$ holomorphic on that ball, integer matrices $A(\lambda)\in M_4(\mathbb{Z})$ for $\lambda\in\mathbb{H}[\mathbb{Q},a,b]$, a set $T\subseteq\mathbb{Z}^4$ and $a_0\in\mathbb{Z}^4$, such that for $\sigma\in\mathcal{U}$ with $\sigma(t)$ in the smaller ball, $u_{\sigma(t)}$ is classified by the chart point $\operatorname{Spec}\sigma$ followed by $j$; and for all $z$ in that ball: the $v_i(z)$ lie in $\kappa(z)\cdot\mathrm{latt}(u_z)$ and every element of $\kappa(z)\cdot\mathrm{latt}(u_z)$ is a unique integral combination of them; $\iota(\lambda)v_{j_0}(z)=\sum_i A(\lambda)_{i j_0}v_i(z)$ for $\lambda\in\Lambda$; the points of $u_z$ factoring through its level-$N$ structure are exactly the classes of $\kappa(z)^{-1}N^{-1}\sum_i n_i v_i(z)$ with $n\in T$; and the full-level-$m$ point of $u_z$ has $e$-image the class of $\kappa(z)^{-1}m^{-1}\sum_i (a_0)_i v_i(z)$.
--
--   This is the analytic step in the uniformisation of the family of fake elliptic curves over a chart of the fine moduli curve at full level $m$: the period lattices of the algebraic family over a disc move holomorphically, in a frame in which the $\Lambda$-action and the level-$N$ and level-$m$ data are described by constant integral matrices and constant integer vectors. It is used to produce a local period chart with injective period map on the fine moduli curve, via [`CerednikDrinfeld.QM.IsFineModuli.exists_isOpen_injOn_periodChart_fullLevel_of_analytic_of_isEichlerOrder`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_isOpen_injOn_periodChart_fullLevel_of_analytic_of_isEichlerOrder), and the hypothesis pattern here imposes no coprimality between $m$ and $N q q'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_exists_holomorphic_latticeFrame_of_analytic_of_smooth_algebraicChart_noCoprime.lean

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

theorem CerednikDrinfeld.QM.IsFineModuli.exists_holomorphic_latticeFrame_of_analytic_of_smooth_algebraicChart_noCoprime
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

    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (hSc : Algebra.Smooth ℂ Sc) (hΩ : Module.rank Sc (KaehlerDifferential ℂ Sc) = 1)
    (j : Spec (CommRingCat.of Sc) ⟶ M) [IsOpenImmersion j]
    (hj : j ≫ πM = Spec.map (CommRingCat.ofHom (algebraMap ℂ Sc)))

    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ)) (hr : 0 < r) (hσ₀ : σ₀ ∈ 𝒰)
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t)) :
    ∃ (ε : ℝ) (u : ℂ → FakeEllipticCurve.WithFullLevel Λ N m ℂ) (κ : ℂ → ℂ) (v : Fin 4 → ℂ → (Fin 2 → ℂ))
      (A : ℍ[ℚ, a, b] → Fin 4 → Fin 4 → ℤ) (T : Set (Fin 4 → ℤ)) (a₀ : Fin 4 → ℤ),
      0 < ε ∧ ε ≤ r ∧

      (∀ z ∈ Metric.ball (σ₀ t) ε, κ z ≠ 0) ∧

      (∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₀ t) ε →
        ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) πM,
          x.1 = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ j →
          ptF ℂ (𝟙 (Spec (CommRingCat.of ℂ))) (u (σ t)) = x) ∧

      (∀ i : Fin 4, DifferentiableOn ℂ (v i) (Metric.ball (σ₀ t) ε)) ∧

      (∀ z ∈ Metric.ball (σ₀ t) ε,
        (∀ i : Fin 4, v i z ∈ κ z • latt (u z).1) ∧
        ∀ x ∈ κ z • latt (u z).1, ∃! n : Fin 4 → ℤ, (∑ i, (n i : ℂ) • v i z) = x) ∧

      (∀ z ∈ Metric.ball (σ₀ t) ε, ∀ lam ∈ Λ, ∀ j₀ : Fin 4,
        ((ι lam).map (algebraMap ℝ ℂ)).mulVec (v j₀ z) = ∑ i, (A lam i j₀ : ℂ) • v i z) ∧

      (∀ z ∈ Metric.ball (σ₀ t) ε, ∀ w : Fin 2 → ℂ,
        (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u z).1.f,
            FactorsThrough (u z).1.lev P ∧ e (u z).1 P = (w : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup)) ↔
          ∃ n ∈ T, (w : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup) =
            (((κ z)⁻¹ • (((N : ℂ)⁻¹) • ∑ i, (n i : ℂ) • v i z) : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup)) ∧

      (∀ z ∈ Metric.ball (σ₀ t) ε,
        e (u z).1 (u z).2.P =
          (((κ z)⁻¹ • (((m : ℂ)⁻¹) • ∑ i, (a₀ i : ℂ) • v i z) : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup)) := by sorry
