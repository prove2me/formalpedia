-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isLocalHom_differentiableOn_uniformization_family_near_zero
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isLocalHom_differentiableOn_uniformization_family_near_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/26d399aa-c397-5f8f-859c-1e0105bc6aad
-- title:
--   Rescaled fibrewise uniformisation, jointly holomorphic near the identity
-- statement:
--   Throughout, $q$ and $q'$ are primes and $a,b\in\mathbb{Q}$ are such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $a>0$ or $b>0$, and for every height-one prime $v$ of $\mathbb{Q}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra (every non-zero element is a unit) exactly when $v$ contains $q$ or $q'$; moreover $q'\neq q$. Here $\Lambda$ is a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order (an order maximal for inclusion among orders), and $\iota:\mathbb{H}[\mathbb{Q},a,b]\to M_2(\mathbb{R})$ is an injective $\mathbb{Q}$-algebra map. A level $N\neq 0$ is fixed with $q\nmid N$, $q'\nmid N$ and $N$ squarefree, together with a $\mathbb{Z}$-submodule $R\subseteq\Lambda$ which is an Eichler order of level $N$, i.e. $R=\Lambda_1\cap\Lambda_2$ for maximal orders $\Lambda_1,\Lambda_2$ with relative index $N$ of $R$ in $\Lambda_1$.
--
--   For a commutative ring $S$, an object of `FakeEllipticCurve Λ N S` consists of a scheme $A$ with a structure morphism $f:A\to\operatorname{Spec}S$, a commutative relative group law $L$ on $f$ (fibrewise group structure on the sets `SchemeHomOver t f` of sections $\varphi$ with $\varphi\circ t$-compatibility $\varphi\gg f=t$, functorial in the base change $t$), an abelian-scheme property bundle for $f$, the requirement that every fibre has topological Krull dimension $2$, an action `act` of $\Lambda$ by endomorphisms of $A$ over $S$ which are group-law homomorphisms, are unital, multiplicative and additive in the acting element and satisfy a trace condition on tangent spaces at geometric points, and further level-$N$ structure data ($C$, `lev`, …).
--
--   The first group of hypotheses is the fibrewise analytic dictionary for fake elliptic curves over $\mathbb{C}$. A map `latt` assigns to each $E\in$ `FakeEllipticCurve Λ N ℂ` a $\mathbb{Z}$-submodule $\mathrm{latt}(E)\subseteq\mathbb{C}^2$, and `e` gives for each such $E$ a bijection $e_E$ from the set of $\mathbb{C}$-points of $E$ over $\operatorname{Spec}\mathbb{C}$ (sections of $E.f$ over the identity of $\operatorname{Spec}\mathbb{C}$) onto $\mathbb{C}^2/\mathrm{latt}(E)$. These are subject to: `hL1`, that $\mathrm{latt}(E)$ is the $\mathbb{Z}$-span of the range of some $\mathbb{R}$-basis of $\mathbb{C}^2$ indexed by `Fin 4`, and is stable under $v\mapsto \iota(x)_{\mathbb{C}}\,v$ for all $x\in\Lambda$; `hE1`, that $e_E$ carries the group law $L$ on $\mathbb{C}$-points to addition; `hE2`, that if $e_E(P)$ is the class of $v$ then $e_E$ of the push-forward of $P$ along $E.\mathrm{act}(x)$ is the class of $\iota(x)_{\mathbb{C}}\,v$, for $x\in\Lambda$; `hH1`, that for $\varphi:E.A\to E'.A$ with $\varphi\gg E'.f=E.f$ which is a group-law homomorphism for all base changes and commutes with the $\Lambda$-actions, there is $c\in\mathbb{C}$ with $c\cdot\mathrm{latt}(E)\subseteq\mathrm{latt}(E')$ such that $\varphi$ acts on $\mathbb{C}$-points, in the coordinates $e_E,e_{E'}$, as multiplication by $c$; `hH2`, the converse existence statement, that every $c$ with $c\cdot\mathrm{latt}(E)\subseteq\mathrm{latt}(E')$ is realised by such a $\varphi$ over $\operatorname{Spec}\mathbb{C}$ which is a group-law homomorphism, is $\Lambda$-equivariant and induces multiplication by $c$; `hH3`, rigidity: two morphisms $E.A\to E'.A$ over the base inducing the same map on $\mathbb{C}$-points are equal; `hAN`, that for every $E$, every open $U\subseteq E.A$ and every $f\in\Gamma(E.A,U)$ the locus of $v\in\mathbb{C}^2$ for which the $\mathbb{C}$-point $e_E^{-1}([v])$ factors through $U$ is open, and there is $F:\mathbb{C}^2\to\mathbb{C}$, differentiable on that locus, whose value at $v$ is the evaluation of $f$ at $e_E^{-1}([v])$ (via `appLE` and the identification $\Gamma(\operatorname{Spec}\mathbb{C},\top)\cong\mathbb{C}$); and `hCOV`, that for every $E$ and every $v_0\in\mathbb{C}^2$ there are an open $U$, two sections $f_1,f_2\in\Gamma(E.A,U)$, a radius $\varepsilon>0$, a continuous $\mathbb{C}$-linear automorphism $D$ of $\mathbb{C}^2$ and a map $F:\mathbb{C}^2\to\mathbb{C}^2$ such that all points $e_E^{-1}([v])$ with $v$ in the ball $B(v_0,\varepsilon)$ factor through $U$, $F(v)$ is the pair of evaluations of $f_1,f_2$ at $e_E^{-1}([v])$ there, and $F$ has Fréchet derivative $D$ at $v_0$.
--
--   The second group of hypotheses is an analytic chart on a smooth affine curve: $Sc$ is a $\mathbb{C}$-algebra which is a finite-type domain, smooth over $\mathbb{C}$, with $\operatorname{rank}_{Sc}\Omega_{Sc/\mathbb{C}}=1$; $t\in Sc$, $\sigma_0:Sc\to\mathbb{C}$ a $\mathbb{C}$-algebra map, $r>0$, and $\mathcal{U}$ a set of $\mathbb{C}$-algebra maps $Sc\to\mathbb{C}$ containing $\sigma_0$ such that $\sigma\mapsto\sigma(t)$ is a bijection of $\mathcal{U}$ onto the ball $B(\sigma_0(t),r)$, and such that for every $s\in Sc$ there is a function $F$ on $\mathbb{C}$, differentiable on $B(\sigma_0(t),r)$, with $\sigma(s)=F(\sigma(t))$ for all $\sigma\in\mathcal{U}$.
--
--   The third group of hypotheses is the family: $\mathcal{A}\in$ `FakeEllipticCurve Λ N Sc`, a map $E:\mathbb{C}\to$ `FakeEllipticCurve Λ N ℂ`, morphisms $g(z):(E\,z).A\to\mathcal{A}.A$, and `hg`, which asserts for each $\sigma\in\mathcal{U}$ that the square formed by $g(\sigma(t))$, $(E(\sigma(t))).f$, $\mathcal{A}.f$ and $\operatorname{Spec}(\sigma)$ is cartesian, and — with that cartesian square at hand — that $g(\sigma(t))$ carries the group law of $E(\sigma(t))$ on $\mathbb{C}$-points over $\operatorname{Spec}\mathbb{C}$ to the group law of $\mathcal{A}$ over $\operatorname{Spec}(\sigma)$, and that $(E(\sigma(t))).\mathrm{act}(x)$ followed by $g(\sigma(t))$ equals $g(\sigma(t))$ followed by $\mathcal{A}.\mathrm{act}(x)$ for every $x\in\Lambda$.
--
--   Conclusion. There exist $\varepsilon\in\mathbb{R}$, a function $\kappa:\mathbb{C}\to\mathbb{C}$ and $r'\in\mathbb{R}$ with $0<\varepsilon\le r$ and $0<r'$, such that the following hold. Write $\Pi(\sigma,w)$ for the composite of the $\mathbb{C}$-point $e_{E(\sigma(t))}^{-1}\bigl([\kappa(\sigma(t))\,w]\bigr)$ with $g(\sigma(t))$.
--
--   (i) $\kappa(z)\neq 0$ for every $z\in B(\sigma_0(t),\varepsilon)$.
--
--   (ii) For every $\sigma\in\mathcal{U}$, the map induced by $g(\sigma(t))$ on $\mathbb{C}$-points over $\operatorname{Spec}\mathbb{C}$ is injective: if $P,Q$ are sections of $(E(\sigma(t))).f$ over the identity with $P_1\gg g(\sigma(t))=Q_1\gg g(\sigma(t))$, then $P=Q$.
--
--   (iii) For every $\sigma\in\mathcal{U}$ with $\sigma(t)\in B(\sigma_0(t),\varepsilon)$ and every $w\in\mathbb{C}^2$: $\Pi(\sigma,w)$ equals the underlying morphism of the identity section $\mathcal{A}.L.\mathrm{one}$ over $\operatorname{Spec}(\sigma)$ if and only if $\kappa(\sigma(t))\,w\in\mathrm{latt}(E(\sigma(t)))$.
--
--   (iv) For every $\sigma\in\mathcal{U}$ and every $w\in\mathbb{C}^2$, $\Pi(\sigma,w)$ followed by $\mathcal{A}.f$ equals $\operatorname{Spec}(\sigma)$; that is, $\Pi(\sigma,w)$ is a point of $\mathcal{A}$ over $\sigma$.
--
--   (v) For every $\sigma\in\mathcal{U}$ and all $w,w'\in\mathbb{C}^2$, given the witnesses from (iv) that $\Pi(\sigma,w)$ and $\Pi(\sigma,w')$ lie over $\operatorname{Spec}(\sigma)$, the product of these two points under $\mathcal{A}.L$ over $\operatorname{Spec}(\sigma)$ is $\Pi(\sigma,w+w')$; thus $w\mapsto\Pi(\sigma,w)$ is additive.
--
--   (vi) For every open $V\subseteq\mathcal{A}.A$ and every $f\in\Gamma(\mathcal{A}.A,V)$: the set of pairs $(z,w)\in\mathbb{C}\times\mathbb{C}^2$ with $z\in B(\sigma_0(t),\varepsilon)$, $w\in B(0,r')$ and such that some $\sigma\in\mathcal{U}$ has $\sigma(t)=z$ and $\Pi(\sigma,w)$ factoring through $V$, is open; and there is $F:\mathbb{C}\times\mathbb{C}^2\to\mathbb{C}$, differentiable on that set, with $F(\sigma(t),w)$ equal to the evaluation of $f$ at $\Pi(\sigma,w)$ (via `appLE` and $\Gamma(\operatorname{Spec}\mathbb{C},\top)\cong\mathbb{C}$) for all $\sigma\in\mathcal{U}$ with $\sigma(t)\in B(\sigma_0(t),\varepsilon)$, all $w\in B(0,r')$ and every witness that $\Pi(\sigma,w)$ factors through $V$. So the pulled-back regular functions are jointly holomorphic in the base parameter and the uniformising variable near the zero section.
--
--   (vii) For every $\sigma_1\in\mathcal{U}$ with $\sigma_1(t)\in B(\sigma_0(t),\varepsilon)$ and every $w_1\in\mathbb{C}^2$ (no smallness of $w_1$ required) there exist an open $V\subseteq\mathcal{A}.A$, sections $f_2,f_3\in\Gamma(\mathcal{A}.A,V)$, a radius $\delta>0$, a continuous $\mathbb{C}$-linear automorphism $D$ of $\mathbb{C}^2$ and a map $F:\mathbb{C}^2\to\mathbb{C}^2$ such that $\Pi(\sigma_1,w)$ factors through $V$ for all $w\in B(w_1,\delta)$, $F(w)$ is the pair of evaluations of $f_2$ and $f_3$ at $\Pi(\sigma_1,w)$ for such $w$, and $F$ has Fréchet derivative $D$ at $w_1$; that is, $(f_2,f_3)$ is a holomorphic chart with invertible derivative along the fibre at $w_1$.
--
--   This is the relative exponential map for an algebraic family of fake elliptic curves over a smooth affine curve: after a base-point-dependent rescaling $\kappa$ of the uniformising coordinate, the fibrewise uniformisations $\mathbb{C}^2\to\mathcal{A}_\sigma$ fit together into a map whose composites with regular functions are holomorphic jointly in the base parameter and the fibre coordinate near the identity section, and which is a local chart along each fibre. It is used in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_differentiableOn_eval_comp_uniformization_family_of_smooth_of_analytic`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_differentiableOn_eval_comp_uniformization_family_of_smooth_of_analytic), within the analytic description of quaternionic (Shimura) curves and their fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isLocalHom_differentiableOn_uniformization_family_near_zero.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isLocalHom_differentiableOn_uniformization_family_near_zero
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
    ∃ (ε : ℝ) (κ : ℂ → ℂ) (r' : ℝ), 0 < ε ∧ ε ≤ r ∧ 0 < r' ∧ (∀ z ∈ Metric.ball (σ₀ t) ε, κ z ≠ 0) ∧

      (∀ σ ∈ 𝒰, ∀ (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (E (σ t)).f),
        P.1 ≫ g (σ t) = Q.1 ≫ g (σ t) → P = Q) ∧

      (∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₀ t) ε → ∀ w : Fin 2 → ℂ,
        (((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) = (𝒜.L.one (Spec.map (CommRingCat.ofHom σ.toRingHom))).1 ↔
          κ (σ t) • w ∈ latt (E (σ t))) ∧

      (∀ σ ∈ 𝒰, ∀ w : Fin 2 → ℂ, (((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ≫ 𝒜.f = Spec.map (CommRingCat.ofHom σ.toRingHom)) ∧

      (∀ σ ∈ 𝒰, ∀ (w w' : Fin 2 → ℂ)
        (hw : (((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ≫ 𝒜.f = Spec.map (CommRingCat.ofHom σ.toRingHom))
        (hw' : (((e (E (σ t))).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ≫ 𝒜.f = Spec.map (CommRingCat.ofHom σ.toRingHom)),
        (𝒜.L.mul (Spec.map (CommRingCat.ofHom σ.toRingHom)) ⟨(((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)), hw⟩ ⟨(((e (E (σ t))).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)), hw'⟩).1 =
          (((e (E (σ t))).symm ((κ (σ t) • (w + w') : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t))) ∧

      (∀ (V : 𝒜.A.Opens) (f : Γ(𝒜.A, V)),
        IsOpen {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ p.2 ∈ Metric.ball (0 : Fin 2 → ℂ) r' ∧
          ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V} ∧
        ∃ F : ℂ × (Fin 2 → ℂ) → ℂ,
          DifferentiableOn ℂ F {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ p.2 ∈ Metric.ball (0 : Fin 2 → ℂ) r' ∧
            ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V} ∧
          ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₀ t) ε → ∀ w ∈ Metric.ball (0 : Fin 2 → ℂ) r', ∀ (hV : ⊤ ≤ (((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V),
            F (σ t, w) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((((e (E (σ t))).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ t))).toAddSubgroup)).1 ≫ g (σ t))).appLE V ⊤ hV) f)) ∧

      (∀ σ₁ ∈ 𝒰, σ₁ t ∈ Metric.ball (σ₀ t) ε → ∀ w₁ : Fin 2 → ℂ,
        ∃ (V : 𝒜.A.Opens) (f₂ f₃ : Γ(𝒜.A, V)) (δ : ℝ) (D : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ))
          (F : (Fin 2 → ℂ) → (Fin 2 → ℂ)),
          0 < δ ∧
          (∀ w ∈ Metric.ball w₁ δ, ⊤ ≤ (((e (E (σ₁ t))).symm ((κ (σ₁ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ₁ t))).toAddSubgroup)).1 ≫ g (σ₁ t)) ⁻¹ᵁ V) ∧
          (∀ (w : Fin 2 → ℂ) (hV : ⊤ ≤ (((e (E (σ₁ t))).symm ((κ (σ₁ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ₁ t))).toAddSubgroup)).1 ≫ g (σ₁ t)) ⁻¹ᵁ V), w ∈ Metric.ball w₁ δ →
            F w = ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((((e (E (σ₁ t))).symm ((κ (σ₁ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ₁ t))).toAddSubgroup)).1 ≫ g (σ₁ t))).appLE V ⊤ hV) f₂),
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((((e (E (σ₁ t))).symm ((κ (σ₁ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (E (σ₁ t))).toAddSubgroup)).1 ≫ g (σ₁ t))).appLE V ⊤ hV) f₃)]) ∧
          HasFDerivAt F (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) w₁) := by sorry
