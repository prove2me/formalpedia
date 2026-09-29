-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_differentiableOn_eval_comp_uniformization_family_of_smooth_of_analytic
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_differentiableOn_eval_comp_uniformization_family_of_smooth_of_analytic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/4707c160-57bd-5e76-a536-dff68417d48f
-- title:
--   Jointly holomorphic uniformisation of a family of fake elliptic curves
-- statement:
--   Throughout, $a,b\in\mathbb{Q}$ and $q,q'$ are primes with $q'\neq q$, and $\mathbb{H}[\mathbb{Q},a,b]$ denotes the corresponding quaternion algebra over $\mathbb{Q}$.
--
--   **Quaternionic data.** The hypothesis `hB` is `IsIndefiniteRamifiedExactlyAt a b q q'`: either $0<a$ or $0<b$, and for every finite place $v$ of $\mathbb{Q}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ divides $q$ or $q'$. Further, $\Lambda$ is a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is an order maximal among orders (`hΛ`), $\iota$ is an injective $\mathbb{Q}$-algebra map $\mathbb{H}[\mathbb{Q},a,b]\to M_2(\mathbb{R})$, $N$ is a nonzero squarefree natural number divisible by neither $q$ nor $q'$, and $R\leq\Lambda$ is an Eichler order of level $N$, i.e. an intersection $\Lambda_1\cap\Lambda_2$ of two maximal orders with relative index $N$ in $\Lambda_1$ (`hR`).
--
--   A *fake elliptic curve* over a commutative ring $S$ (`FakeEllipticCurve Λ N S`) consists of a scheme $A$ with a morphism $f\colon A\to\operatorname{Spec} S$, a commutative relative group law $L$ on $f$ (a functorial group structure on the sets $\mathrm{SchemeHomOver}\,t\,f$ of $T$-points over $S$), an abelian-scheme property bundle, fibres of topological Krull dimension $2$, an action `act` of $\Lambda$ by endomorphisms of $A$ over $S$ which is additive and multiplicative, respects the group law and satisfies the trace condition relating $\operatorname{tr}$ of the induced map on tangent spaces to $m+\bar m$, together with the level-$N$ data (a scheme $C$ and a morphism `lev`, and the remaining fields of the structure). For a ring $S$ and a point of the base, $\mathrm{SchemeHomOver}\,(\mathbb{1}_{\operatorname{Spec}\mathbb{C}})\,E.f$ is the set of sections of $E.f$, i.e. the $\mathbb{C}$-points of $E$; for such a point $P$ and an open $V$, the condition $\top\le P^{-1}V$ says that $P$ lands in $V$.
--
--   **The fibrewise analytic dictionary over $\mathbb{C}$ (hypotheses).** Given are an assignment $E\mapsto\operatorname{latt}(E)$ of a $\mathbb{Z}$-submodule of $\mathbb{C}^2=(\mathrm{Fin}\,2\to\mathbb{C})$ to each fake elliptic curve $E$ over $\mathbb{C}$, and for each such $E$ a bijection $e_E$ from the $\mathbb{C}$-points of $E$ onto $\mathbb{C}^2/\operatorname{latt}(E)$, subject to:
--
--   - `hL1`: $\operatorname{latt}(E)$ is the $\mathbb{Z}$-span of (the range of) an $\mathbb{R}$-basis of $\mathbb{C}^2$ indexed by $\mathrm{Fin}\,4$, and for $x\in\Lambda$ the matrix $\iota(x)$, with entries pushed into $\mathbb{C}$, carries $\operatorname{latt}(E)$ into itself by `mulVec`;
--
--   - `hE1`: $e_E$ is additive for the group law $E.L$ on $\mathbb{C}$-points;
--
--   - `hE2`: $e_E$ intertwines the action of $x\in\Lambda$ on $\mathbb{C}$-points with multiplication by $\iota(x)$ on $\mathbb{C}^2$;
--
--   - `hH1`: every morphism $\varphi\colon E.A\to E'.A$ over $\operatorname{Spec}\mathbb{C}$ which is compatible with the group laws on $T$-points for all test schemes $T$ and commutes with the $\Lambda$-actions is given by a scalar $c\in\mathbb{C}$ with $c\cdot\operatorname{latt}(E)\subseteq\operatorname{latt}(E')$, in the sense that $e_{E'}$ of the pushforward of a point with coordinate $v$ is the class of $c\cdot v$;
--
--   - `hH2`: conversely, every scalar $c$ with $c\cdot\operatorname{latt}(E)\subseteq\operatorname{latt}(E')$ is realised by such a morphism $\varphi$ over $\operatorname{Spec}\mathbb{C}$, compatible with the group laws on all $T$-points, $\Lambda$-equivariant, and inducing $v\mapsto c\cdot v$;
--
--   - `hH3`: two morphisms $E.A\to E'.A$ over $\operatorname{Spec}\mathbb{C}$ agreeing on all $\mathbb{C}$-points are equal;
--
--   - `hAN`: for every $E$, every open $U\subseteq E.A$ and every $f\in\Gamma(E.A,U)$, the set of $v\in\mathbb{C}^2$ whose point $e_E^{-1}([v])$ lands in $U$ is open, and there is $F\colon\mathbb{C}^2\to\mathbb{C}$, complex differentiable on that set, whose value at $v$ is the pullback of $f$ along $e_E^{-1}([v])$ (read through $\Gamma$–$\operatorname{Spec}$ adjunction);
--
--   - `hCOV`: for every $E$ and every $v_0\in\mathbb{C}^2$ there exist an open $U\subseteq E.A$, sections $f_1,f_2\in\Gamma(E.A,U)$, a radius $\varepsilon>0$, a continuous $\mathbb{C}$-linear automorphism $D$ of $\mathbb{C}^2$ and a map $F\colon\mathbb{C}^2\to\mathbb{C}^2$ such that all $v$ in the ball of radius $\varepsilon$ about $v_0$ give points landing in $U$, $F$ is there the pair of pullbacks of $f_1,f_2$, and $F$ has Fréchet derivative $D$ at $v_0$.
--
--   **The analytic chart (hypotheses).** $S_c$ is a finitely generated smooth $\mathbb{C}$-algebra which is a domain with $\operatorname{rank}_{S_c}\Omega_{S_c/\mathbb{C}}=1$; $t\in S_c$, $\sigma_0\colon S_c\to\mathbb{C}$ is a $\mathbb{C}$-algebra map, $r>0$, and $\mathcal{U}$ is a set of $\mathbb{C}$-points of $S_c$ containing $\sigma_0$ on which $\sigma\mapsto\sigma(t)$ is a bijection onto the ball $B(\sigma_0(t),r)$ (`hbij`), such that every $s\in S_c$ is holomorphic in this coordinate: there is $F$ differentiable on $B(\sigma_0(t),r)$ with $\sigma(s)=F(\sigma(t))$ for all $\sigma\in\mathcal{U}$ (`hhol`).
--
--   **The family (hypotheses).** $\mathcal{A}$ is a fake elliptic curve over $S_c$, $E$ assigns to each $z\in\mathbb{C}$ a fake elliptic curve over $\mathbb{C}$, and $g$ assigns to each $z$ a morphism $g(z)\colon (E\,z).A\to\mathcal{A}.A$. The hypothesis `hg` demands, for each $\sigma\in\mathcal{U}$: the square formed by $g(\sigma(t))$, the structure morphisms of $E(\sigma(t))$ and $\mathcal{A}$, and $\operatorname{Spec}$ of $\sigma$ is cartesian; $g(\sigma(t))$ carries the group law of $E(\sigma(t))$ on $\mathbb{C}$-points to the relative group law of $\mathcal{A}$ over $\operatorname{Spec}$ of $\sigma$ (note that, unlike the project's `IsPullback`, this compatibility is required only for $\mathbb{C}$-points, not for all test schemes, and no compatibility of level structures is required); and $g(\sigma(t))$ is $\Lambda$-equivariant, $E(\sigma(t)).\mathrm{act}\,x$ followed by $g(\sigma(t))$ equalling $g(\sigma(t))$ followed by $\mathcal{A}.\mathrm{act}\,x$ for all $x\in\Lambda$.
--
--   **Conclusion.** There exist $\varepsilon\in\mathbb{R}$ and $\kappa\colon\mathbb{C}\to\mathbb{C}$ with $0<\varepsilon\le r$ and $\kappa(z)\neq0$ for all $z\in B(\sigma_0(t),\varepsilon)$, such that, writing $\Pi(\sigma,w)$ for the $\mathbb{C}$-point $e_{E(\sigma(t))}^{-1}([\kappa(\sigma(t))\cdot w])$ of $E(\sigma(t))$ followed by $g(\sigma(t))$, the following four assertions hold.
--
--   (i) *Joint analyticity.* For every open $V\subseteq\mathcal{A}.A$ and every $f\in\Gamma(\mathcal{A}.A,V)$: the set of pairs $p\in\mathbb{C}\times\mathbb{C}^2$ with $p_1\in B(\sigma_0(t),\varepsilon)$ for which there is $\sigma\in\mathcal{U}$ with $\sigma(t)=p_1$ and $\Pi(\sigma,p_2)$ landing in $V$ is open; and there is $F\colon\mathbb{C}\times\mathbb{C}^2\to\mathbb{C}$, complex differentiable on that set, with $F(\sigma(t),w)$ equal to the pullback of $f$ along $\Pi(\sigma,w)$ for every $\sigma\in\mathcal{U}$ with $\sigma(t)\in B(\sigma_0(t),\varepsilon)$ and every $w$ for which $\Pi(\sigma,w)$ lands in $V$.
--
--   (ii) *Joint charts separating a pair of points.* For every $\sigma_1\in\mathcal{U}$ with $\sigma_1(t)\in B(\sigma_0(t),\varepsilon)$ and every $w_1,w_1'\in\mathbb{C}^2$ with $\Pi(\sigma_1,w_1)=\Pi(\sigma_1,w_1')$ as morphisms, there exist an open $V\subseteq\mathcal{A}.A$, sections $f_2,f_3\in\Gamma(\mathcal{A}.A,V)$, a radius $\delta>0$, continuous $\mathbb{C}$-linear automorphisms $D,D'$ of $\mathbb{C}\times\mathbb{C}^2$ and a map $\Phi\colon\mathbb{C}\times\mathbb{C}^2\to\mathbb{C}\times\mathbb{C}^2$ such that: $\Pi(\sigma_1,w_1)$ lands in $V$; every $p$ in the $\delta$-ball about $(\sigma_1(t),w_1)$, and likewise every $p$ in the $\delta$-ball about $(\sigma_1(t),w_1')$, satisfies $p_1\in B(\sigma_0(t),\varepsilon)$ and admits $\sigma\in\mathcal{U}$ with $\sigma(t)=p_1$ and $\Pi(\sigma,p_2)$ landing in $V$; for $\sigma\in\mathcal{U}$ and $w$ with $(\sigma(t),w)$ in either of the two balls, $\Phi(\sigma(t),w)$ equals $(\sigma(t),\,[\,\text{pullback of }f_2,\ \text{pullback of }f_3\,])$ along $\Pi(\sigma,w)$; $\Phi$ has Fréchet derivative $D$ at $(\sigma_1(t),w_1)$ and $D'$ at $(\sigma_1(t),w_1')$; and, for $\sigma\in\mathcal{U}$ and $w,w'$ with $(\sigma(t),w)$ in the first ball and $(\sigma(t),w')$ in the second, if the pullbacks of $f_2$ along $\Pi(\sigma,w)$ and $\Pi(\sigma,w')$ agree and likewise for $f_3$, then $\Pi(\sigma,w)=\Pi(\sigma,w')$.
--
--   (iii) *Uniform discreteness of the rescaled lattices near $\sigma_0$.* For every $w\in\mathbb{C}^2$ with $\kappa(\sigma_0(t))\cdot w\notin\operatorname{latt}(E(\sigma_0(t)))$ there is $\delta>0$ such that for all $z\in B(\sigma_0(t),\delta)$ and all $w'\in\mathbb{C}^2$ with $\kappa(z)\cdot w'\in\operatorname{latt}(E\,z)$ one has $\delta\le\lVert w'-w\rVert$.
--
--   (iv) *Local recognition of points in the image.* For every $\sigma_1\in\mathcal{U}$ with $\sigma_1(t)\in B(\sigma_0(t),\varepsilon)$, every $w_1\in\mathbb{C}^2$ and every $\rho>0$ there exist an open $V\subseteq\mathcal{A}.A$, a finite set $fs$ of sections in $\Gamma(\mathcal{A}.A,V)$, a radius $\varepsilon_1>0$ and the fact that $\Pi(\sigma_1,w_1)$ lands in $V$, such that for every $\sigma\in\mathcal{U}$ with $\sigma(t)\in B(\sigma_1(t),\varepsilon_1)$ and every $\mathbb{C}$-point $P$ of $E(\sigma(t))$ whose image under $g(\sigma(t))$ lands in $V$: if for each $\varphi\in fs$ the pullback of $\varphi$ along $P$ followed by $g(\sigma(t))$ differs from its pullback along $\Pi(\sigma_1,w_1)$ by less than $\varepsilon_1$ in absolute value, then there is $w$ in the ball of radius $\rho$ about $w_1$ with $e_{E(\sigma(t))}(P)=[\kappa(\sigma(t))\cdot w]$.
--
--   This is the relative exponential map for a family of fake elliptic curves: the fibrewise complex uniformisations $\mathbb{C}^2/\operatorname{latt}(E_z)\cong E_z(\mathbb{C})$ are shown, after a pointwise rescaling $\kappa(z)$ (no regularity of $\kappa$ being asserted), to assemble into a map holomorphic jointly in the base coordinate and the uniformising variable over an algebraic chart of the base, with joint local charts that separate a prescribed pair of points of a fibre, uniform discreteness of the rescaled lattices, and a local criterion for a point of a fibre to be of the form $\Pi(\sigma,w)$. It is used in the construction of holomorphic lattice frames over fine moduli of fake elliptic curves, in the Čerednik–Drinfel'd part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_differentiableOn_eval_comp_uniformization_family_of_smooth_of_analytic.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_differentiableOn_eval_comp_uniformization_family_of_smooth_of_analytic
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

    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (hSc : Algebra.Smooth ℂ Sc) (hΩ : Module.rank Sc (KaehlerDifferential ℂ Sc) = 1)
    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ)) (hr : 0 < r) (hσ₀ : σ₀ ∈ 𝒰)
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t))

    (𝒜 : FakeEllipticCurve Λ N Sc)
    (E : ℂ → FakeEllipticCurve Λ N ℂ) (g : ∀ z : ℂ, (E z).A ⟶ 𝒜.A)
    (hg : ∀ σ ∈ 𝒰,
      ∃ hc : CategoryTheory.IsPullback (g (σ t)) (E (σ t)).f 𝒜.f (Spec.map (CommRingCat.ofHom σ.toRingHom)),

        (∀ (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (E (σ t)).f),
          ((E (σ t)).L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q).1 ≫ g (σ t) =
            (𝒜.L.mul (𝟙 (Spec (CommRingCat.of ℂ)) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
              ⟨P.1 ≫ g (σ t), by rw [Category.assoc, hc.w, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ g (σ t), by rw [Category.assoc, hc.w, ← Category.assoc, Q.2]⟩).1) ∧

        (∀ x : ↥Λ, (E (σ t)).act x ≫ g (σ t) = g (σ t) ≫ 𝒜.act x)) :
    ∃ (ε : ℝ) (κ : ℂ → ℂ), 0 < ε ∧ ε ≤ r ∧ (∀ z ∈ Metric.ball (σ₀ t) ε, κ z ≠ 0) ∧

      (∀ (V : 𝒜.A.Opens) (f : Γ(𝒜.A, V)),
        IsOpen {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
          ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫
                  g (σ t)) ⁻¹ᵁ V} ∧
        ∃ F : ℂ × (Fin 2 → ℂ) → ℂ,
          DifferentiableOn ℂ F {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
            ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫
                    g (σ t)) ⁻¹ᵁ V} ∧
          ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₀ t) ε → ∀ (w : Fin 2 → ℂ)
            (hV : ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫
                    g (σ t)) ⁻¹ᵁ V),
            F (σ t, w) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
              (((((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫
                  g (σ t)).appLE V ⊤ hV) f)) ∧

      (∀ σ₁ ∈ 𝒰, σ₁ t ∈ Metric.ball (σ₀ t) ε → ∀ w₁ w₁' : Fin 2 → ℂ,
        (((e (E (σ₁ t))).symm ((κ (σ₁ t) • w₁ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ₁ t))).toAddSubgroup)).1 ≫ g (σ₁ t)) =
          (((e (E (σ₁ t))).symm ((κ (σ₁ t) • w₁' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ₁ t))).toAddSubgroup)).1 ≫ g (σ₁ t)) →
        ∃ (V : 𝒜.A.Opens) (f₂ f₃ : Γ(𝒜.A, V)) (δ : ℝ)
          (D D' : (ℂ × (Fin 2 → ℂ)) ≃L[ℂ] (ℂ × (Fin 2 → ℂ))) (Φ : ℂ × (Fin 2 → ℂ) → ℂ × (Fin 2 → ℂ)),
          0 < δ ∧
          ⊤ ≤ (((e (E (σ₁ t))).symm ((κ (σ₁ t) • w₁ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ₁ t))).toAddSubgroup)).1 ≫ g (σ₁ t)) ⁻¹ᵁ V ∧
          (∀ p ∈ Metric.ball ((σ₁ t, w₁) : ℂ × (Fin 2 → ℂ)) δ, p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
            ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V) ∧
          (∀ p ∈ Metric.ball ((σ₁ t, w₁') : ℂ × (Fin 2 → ℂ)) δ, p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
            ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V) ∧
          (∀ σ ∈ 𝒰, ∀ (w : Fin 2 → ℂ),
            (((σ t, w) : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁) : ℂ × (Fin 2 → ℂ)) δ ∨ ((σ t, w) : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁') : ℂ × (Fin 2 → ℂ)) δ) →
            ∀ (hV : ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V),
            Φ (σ t, w) = (σ t, ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV) f₂),
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV) f₃)])) ∧
          HasFDerivAt Φ (D : (ℂ × (Fin 2 → ℂ)) →L[ℂ] (ℂ × (Fin 2 → ℂ))) (σ₁ t, w₁) ∧
          HasFDerivAt Φ (D' : (ℂ × (Fin 2 → ℂ)) →L[ℂ] (ℂ × (Fin 2 → ℂ))) (σ₁ t, w₁') ∧
          (∀ σ ∈ 𝒰, ∀ (w w' : Fin 2 → ℂ),
            ((σ t, w) : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁) : ℂ × (Fin 2 → ℂ)) δ →
            ((σ t, w') : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁') : ℂ × (Fin 2 → ℂ)) δ →
            ∀ (hV : ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V)
              (hV' : ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V),
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV) f₂) =
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (E (σ t))).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV') f₂) →
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV) f₃) =
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (E (σ t))).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV') f₃) →
              (((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) =
                (((e (E (σ t))).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)))) ∧

      (∀ w : Fin 2 → ℂ, κ (σ₀ t) • w ∉ latt (E (σ₀ t)) →
        ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Metric.ball (σ₀ t) δ, ∀ w' : Fin 2 → ℂ,
          κ z • w' ∈ latt (E z) → δ ≤ ‖w' - w‖) ∧

      (∀ σ₁ ∈ 𝒰, σ₁ t ∈ Metric.ball (σ₀ t) ε → ∀ (w₁ : Fin 2 → ℂ) (ρ : ℝ), 0 < ρ →
        ∃ (V : 𝒜.A.Opens) (fs : Finset ↑(Γ(𝒜.A, V))) (ε₁ : ℝ)
          (h₁ : ⊤ ≤ (((e (E (σ₁ t))).symm ((κ (σ₁ t) • w₁ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ₁ t))).toAddSubgroup)).1 ≫ g (σ₁ t)) ⁻¹ᵁ V),
          0 < ε₁ ∧ ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε₁ →
            ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (E (σ t)).f)
              (hP : ⊤ ≤ (P.1 ≫ g (σ t)) ⁻¹ᵁ V),
              (∀ φ ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P.1 ≫ g (σ t)).appLE V ⊤ hP) φ) -
                  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (E (σ₁ t))).symm ((κ (σ₁ t) • w₁ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ₁ t))).toAddSubgroup)).1 ≫ g (σ₁ t)).appLE V ⊤ h₁) φ)‖ < ε₁) →
              ∃ w ∈ Metric.ball w₁ ρ,
                e (E (σ t)) P = ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)) := by sorry
