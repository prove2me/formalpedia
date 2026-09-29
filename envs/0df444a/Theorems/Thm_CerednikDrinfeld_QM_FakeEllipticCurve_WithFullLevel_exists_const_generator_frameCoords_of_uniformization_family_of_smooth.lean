-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_const_generator_frameCoords_of_uniformization_family_of_smooth
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_const_generator_frameCoords_of_uniformization_family_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/ac065592-442f-589b-be27-6d7a294daeb5
-- title:
--   Constant frame coordinates for the full level-m generator
-- statement:
--   Throughout, $a,b\in\mathbb{Q}$ and $q,q'$ are primes with $q'\neq q$, and the hypothesis `hB` asserts `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all its nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Further, $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ is a $\mathbb{Z}$-submodule which is a maximal order (an order, and the only order containing it), $\iota:\mathbb{H}[\mathbb{Q},a,b]\to M_2(\mathbb{R})$ is an injective $\mathbb{Q}$-algebra map, $N$ is a nonzero squarefree natural number divisible by neither $q$ nor $q'$, and $R\leq\Lambda$ is an Eichler order of level $N$, i.e. an intersection $\Lambda_1\cap\Lambda_2$ of two maximal orders whose relative index in $\Lambda_1$ is $N$.
--
--   **Uniformisation data for fake elliptic curves over $\mathbb{C}$.** A map `latt` assigns to every $E:$ `FakeEllipticCurve Λ N ℂ` a $\mathbb{Z}$-submodule $\mathrm{latt}(E)\subseteq\mathbb{C}^2$, and `e` assigns to every such $E$ a bijection between the $\mathbb{C}$-points of $E$ (sections of `E.f` over the identity of $\operatorname{Spec}\mathbb{C}$) and $\mathbb{C}^2/\mathrm{latt}(E)$. The hypotheses on these are: `hL1`, that $\mathrm{latt}(E)$ is the $\mathbb{Z}$-span of the range of an $\mathbb{R}$-basis of $\mathbb{C}^2$ indexed by `Fin 4` and is stable under $v\mapsto \iota(x)_{\mathbb{C}}\,v$ for all $x\in\Lambda$; `hE1`, that `e E` carries the relative group law `E.L.mul` on $\mathbb{C}$-points to addition in the quotient; `hE2`, that `e E` carries the action of $x\in\Lambda$ on points, $P\mapsto$ `pushPt (E.act x) _ P`, to $v\mapsto \iota(x)_{\mathbb{C}}\,v$ modulo $\mathrm{latt}(E)$; `hH1`, that every morphism $\varphi:E.A\to E'.A$ over $\operatorname{Spec}\mathbb{C}$ which is a homomorphism for the group laws on $T$-points for all test schemes and commutes with the $\Lambda$-actions is induced by some $c\in\mathbb{C}$ with $c\cdot\mathrm{latt}(E)\subseteq\mathrm{latt}(E')$, in the sense that `e E'` of $P$ composed with $\varphi$ is the class of $c\,v$ whenever `e E P` is the class of $v$; `hH2`, the converse, that each such $c$ arises from a morphism $\varphi$ with these three properties; `hH3`, that two morphisms $E.A\to E'.A$ over $\operatorname{Spec}\mathbb{C}$ inducing the same map on $\mathbb{C}$-points coincide; `hAN`, that for every $E$, every open $U\subseteq E.A$ and every $f\in\Gamma(E.A,U)$ the set of $v\in\mathbb{C}^2$ for which the point $(\mathrm{e}\,E)^{-1}[v]$ factors through $U$ is open and the function sending such $v$ to the value of $f$ at that point (via `Scheme.ΓSpecIso` and `appLE`) agrees with a function differentiable on that set; and `hCOV`, that for every $E$ and every $v_0\in\mathbb{C}^2$ there are an open $U$, two sections $f_1,f_2\in\Gamma(E.A,U)$, a radius $\varepsilon>0$, a continuous $\mathbb{C}$-linear automorphism $D$ of $\mathbb{C}^2$ and a map $F:\mathbb{C}^2\to\mathbb{C}^2$ such that all points coming from the ball $B(v_0,\varepsilon)$ factor through $U$, on that ball $F$ is the pair of values of $f_1,f_2$ at the corresponding point, and $F$ has Fréchet derivative $D$ at $v_0$.
--
--   **The smooth affine base.** $Sc$ is a commutative $\mathbb{C}$-algebra which is a domain, of finite type, smooth over $\mathbb{C}$ (`hSc`), with $\operatorname{rank}_{Sc}\Omega_{Sc/\mathbb{C}}=1$ (`hΩ`); $t\in Sc$, $\sigma_0:Sc\to\mathbb{C}$ is a $\mathbb{C}$-algebra map, $r>0$, and $\mathcal{U}$ is a set of $\mathbb{C}$-algebra maps $Sc\to\mathbb{C}$ containing $\sigma_0$ such that $\sigma\mapsto\sigma(t)$ is a bijection from $\mathcal{U}$ onto the ball $B(\sigma_0(t),r)$ (`hbij`), and such that every $s\in Sc$ is given on $\mathcal{U}$ by a function of $\sigma(t)$ holomorphic on that ball (`hhol`).
--
--   **The family.** $m$ is a natural number, $\mathcal{U}\mathcal{A}$ is an object of `FakeEllipticCurve.WithFullLevel Λ N m Sc`, that is, a fake elliptic curve over $Sc$ together with a full level-$m$ structure (a section $P$ killed by $m$ under the group law, whose geometric specialisations generate the $m$-torsion under $\Lambda$ and whose $\Lambda$-annihilator is $m\Lambda$); $u$ assigns to each $z\in\mathbb{C}$ an object of `FakeEllipticCurve.WithFullLevel Λ N m ℂ`, and $g$ assigns to each $z$ a morphism $(u\,z).1.A\to\mathcal{U}\mathcal{A}.1.A$. The hypothesis `hg` requires, for every $\sigma\in\mathcal{U}$, that $g(\sigma(t))$ make $(u(\sigma(t))).1$ the pullback of $\mathcal{U}\mathcal{A}.1$ along $\operatorname{Spec}(\sigma)$: the square with $g(\sigma(t))$, the two structure morphisms and `Spec.map` of $\sigma$ is a pullback; $g(\sigma(t))$ is compatible with the group laws on $\mathbb{C}$-points; it commutes with the $\Lambda$-actions; it carries points factoring through the level map `lev` of $(u(\sigma(t))).1$ to points factoring through the level map of $\mathcal{U}\mathcal{A}.1$; and the full-level section satisfies $(u(\sigma(t))).2.P$ followed by $g(\sigma(t))$ equals `Spec.map` of $\sigma$ followed by $\mathcal{U}\mathcal{A}.2.P$.
--
--   **Normalisation and relative analytic hypotheses.** $\varepsilon>0$ with $\varepsilon\leq r$, and $\kappa:\mathbb{C}\to\mathbb{C}$ is nowhere zero on $B(\sigma_0(t),\varepsilon)$ (`hκ`). For $\sigma\in\mathcal{U}$ and $w\in\mathbb{C}^2$ write $P_{\sigma,w}$ for the $\mathbb{C}$-point of $(u(\sigma(t))).1$ with `e`-class $\kappa(\sigma(t))\,w$, and $\tilde P_{\sigma,w}$ for $P_{\sigma,w}$ followed by $g(\sigma(t))$. Four hypotheses govern these: `hRELAN` states that for every open $V\subseteq\mathcal{U}\mathcal{A}.1.A$ and every $f\in\Gamma(\mathcal{U}\mathcal{A}.1.A,V)$ the set of pairs $(z,w)$ with $z\in B(\sigma_0(t),\varepsilon)$ and $\tilde P_{\sigma,w}$ factoring through $V$ for some $\sigma\in\mathcal{U}$ with $\sigma(t)=z$ is open, and the value of $f$ at $\tilde P_{\sigma,w}$ is given on it by a function of $(z,w)$ differentiable there. `hRELCOV` (several clauses, summarised here) states that whenever $\sigma_1\in\mathcal{U}$ with $\sigma_1(t)\in B(\sigma_0(t),\varepsilon)$ and $w_1,w_1'$ satisfy $\tilde P_{\sigma_1,w_1}=\tilde P_{\sigma_1,w_1'}$, there are an open $V$, two sections $f_2,f_3$ on $V$, a radius $\delta>0$, two continuous $\mathbb{C}$-linear automorphisms $D,D'$ of $\mathbb{C}\times\mathbb{C}^2$ and a map $\Phi$ on $\mathbb{C}\times\mathbb{C}^2$ such that $\tilde P_{\sigma_1,w_1}$ factors through $V$, both balls of radius $\delta$ about $(\sigma_1(t),w_1)$ and about $(\sigma_1(t),w_1')$ consist of admissible pairs whose associated point factors through $V$, on those balls $\Phi(z,w)=(z,\,(f_2,f_3)\text{-values at }\tilde P_{\sigma,w})$, $\Phi$ has derivative $D$ at $(\sigma_1(t),w_1)$ and $D'$ at $(\sigma_1(t),w_1')$, and the values of $f_2$ and of $f_3$ separate points: if $w,w'$ lie in the respective balls over the same $\sigma$ and the $f_2$-values and the $f_3$-values at $\tilde P_{\sigma,w}$ and $\tilde P_{\sigma,w'}$ agree, then $\tilde P_{\sigma,w}=\tilde P_{\sigma,w'}$. `hKCL` states that if $\kappa(\sigma_0(t))\,w\notin\mathrm{latt}((u(\sigma_0(t))).1)$ then there is $\delta>0$ such that for all $z\in B(\sigma_0(t),\delta)$ and all $w'$ with $\kappa(z)\,w'\in\mathrm{latt}((u\,z).1)$ one has $\|w'-w\|\geq\delta$. `hRELSURJ` states that for $\sigma_1\in\mathcal{U}$ with $\sigma_1(t)\in B(\sigma_0(t),\varepsilon)$, any $w_1\in\mathbb{C}^2$ and any $\rho>0$ there are an open $V$ through which $\tilde P_{\sigma_1,w_1}$ factors, a finite set $fs$ of sections on $V$ and $\varepsilon_1>0$ such that for every $\sigma\in\mathcal{U}$ with $\sigma(t)\in B(\sigma_1(t),\varepsilon_1)$ and every $\mathbb{C}$-point $P$ of $(u(\sigma(t))).1$ whose image under $g(\sigma(t))$ factors through $V$, if all the values at $P$ of the sections in $fs$ are within $\varepsilon_1$ of their values at $\tilde P_{\sigma_1,w_1}$, then the `e`-class of $P$ equals that of $\kappa(\sigma(t))\,w$ for some $w\in B(w_1,\rho)$.
--
--   **The holomorphic frame.** Finally $\varepsilon'$ satisfies $0<\varepsilon'\leq\varepsilon$, and $v_0,\dots,v_3:\mathbb{C}\to\mathbb{C}^2$ are differentiable on $B(\sigma_0(t),\varepsilon')$ (`hv`) and form a frame there (`hbasis`): for every $z$ in that ball, $\kappa(z)\,v_i(z)\in\mathrm{latt}((u\,z).1)$ for each $i$, and every $x\in\mathrm{latt}((u\,z).1)$ has a unique $n\in\mathbb{Z}^4$ with $\sum_i n_i\,v_i(z)=\kappa(z)^{-1}x$.
--
--   **Conclusion.** There exist $\varepsilon''\in\mathbb{R}$ and $a_0\in\mathbb{Z}^4$ such that $0<\varepsilon''$, $\varepsilon''\leq\varepsilon'$, and for every $z\in B(\sigma_0(t),\varepsilon'')$ the full level-$m$ generator of $u\,z$ has uniformisation
--   $$e_{(u\,z).1}\bigl((u\,z).2.P\bigr)=\Bigl[\kappa(z)\cdot m^{-1}\sum_i a_{0,i}\,v_i(z)\Bigr]\in\mathbb{C}^2/\mathrm{latt}((u\,z).1),$$
--   with the same integer vector $a_0$ for all such $z$.
--
--   This is the local constancy, in a holomorphic family of uniformised fake elliptic curves with full level-$m$ structure, of the integral coordinates of the level-$m$ generator with respect to a holomorphically varying frame of the period lattice: the generator is $m$-torsion, hence a fixed rational combination $m^{-1}\sum a_{0,i}v_i(z)$ of the frame vectors near the chosen base point. It is the level-structure clause of the local-constancy package for such families and is cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_const_frameCoords_of_uniformization_family_of_smooth`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_const_frameCoords_of_uniformization_family_of_smooth).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_const_generator_frameCoords_of_uniformization_family_of_smooth.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_const_generator_frameCoords_of_uniformization_family_of_smooth
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

    (m : ℕ) (𝒰𝒜 : FakeEllipticCurve.WithFullLevel Λ N m Sc)
    (u : ℂ → FakeEllipticCurve.WithFullLevel Λ N m ℂ) (g : ∀ z : ℂ, (u z).1.A ⟶ 𝒰𝒜.1.A)
    (hg : ∀ σ ∈ 𝒰,
      ∃ hc : CategoryTheory.IsPullback (g (σ t)) (u (σ t)).1.f 𝒰𝒜.1.f (Spec.map (CommRingCat.ofHom σ.toRingHom)),

      (∀ (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u (σ t)).1.f),
        ((u (σ t)).1.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q).1 ≫ g (σ t) =
          (𝒰𝒜.1.L.mul (𝟙 (Spec (CommRingCat.of ℂ)) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
            ⟨P.1 ≫ g (σ t), by rw [Category.assoc, hc.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g (σ t), by rw [Category.assoc, hc.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, (u (σ t)).1.act x ≫ g (σ t) = g (σ t) ≫ 𝒰𝒜.1.act x) ∧

      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u (σ t)).1.f,
        FactorsThrough (u (σ t)).1.lev P → ∃ P₀ : Spec (CommRingCat.of ℂ) ⟶ 𝒰𝒜.1.C, P₀ ≫ 𝒰𝒜.1.lev = P.1 ≫ g (σ t)) ∧

      ((u (σ t)).2.P).1 ≫ g (σ t) = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (𝒰𝒜.2.P).1)

    (ε : ℝ) (κ : ℂ → ℂ) (hε : 0 < ε) (hεr : ε ≤ r) (hκ : ∀ z ∈ Metric.ball (σ₀ t) ε, κ z ≠ 0)
    (hRELAN :
      (∀ (V : 𝒰𝒜.1.A.Opens) (f : Γ(𝒰𝒜.1.A, V)),
        IsOpen {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
          ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫
                  g (σ t)) ⁻¹ᵁ V} ∧
        ∃ F : ℂ × (Fin 2 → ℂ) → ℂ,
          DifferentiableOn ℂ F {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
            ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫
                    g (σ t)) ⁻¹ᵁ V} ∧
          ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₀ t) ε → ∀ (w : Fin 2 → ℂ)
            (hV : ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫
                    g (σ t)) ⁻¹ᵁ V),
            F (σ t, w) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
              (((((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫
                  g (σ t)).appLE V ⊤ hV) f)))
    (hRELCOV :
      (∀ σ₁ ∈ 𝒰, σ₁ t ∈ Metric.ball (σ₀ t) ε → ∀ w₁ w₁' : Fin 2 → ℂ,
        (((e (u (σ₁ t)).1).symm ((κ (σ₁ t) • w₁ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ₁ t)).1).toAddSubgroup)).1 ≫ g (σ₁ t)) =
          (((e (u (σ₁ t)).1).symm ((κ (σ₁ t) • w₁' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ₁ t)).1).toAddSubgroup)).1 ≫ g (σ₁ t)) →
        ∃ (V : 𝒰𝒜.1.A.Opens) (f₂ f₃ : Γ(𝒰𝒜.1.A, V)) (δ : ℝ)
          (D D' : (ℂ × (Fin 2 → ℂ)) ≃L[ℂ] (ℂ × (Fin 2 → ℂ))) (Φ : ℂ × (Fin 2 → ℂ) → ℂ × (Fin 2 → ℂ)),
          0 < δ ∧
          ⊤ ≤ (((e (u (σ₁ t)).1).symm ((κ (σ₁ t) • w₁ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ₁ t)).1).toAddSubgroup)).1 ≫ g (σ₁ t)) ⁻¹ᵁ V ∧
          (∀ p ∈ Metric.ball ((σ₁ t, w₁) : ℂ × (Fin 2 → ℂ)) δ, p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
            ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V) ∧
          (∀ p ∈ Metric.ball ((σ₁ t, w₁') : ℂ × (Fin 2 → ℂ)) δ, p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
            ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V) ∧
          (∀ σ ∈ 𝒰, ∀ (w : Fin 2 → ℂ),
            (((σ t, w) : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁) : ℂ × (Fin 2 → ℂ)) δ ∨ ((σ t, w) : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁') : ℂ × (Fin 2 → ℂ)) δ) →
            ∀ (hV : ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V),
            Φ (σ t, w) = (σ t, ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV) f₂),
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV) f₃)])) ∧
          HasFDerivAt Φ (D : (ℂ × (Fin 2 → ℂ)) →L[ℂ] (ℂ × (Fin 2 → ℂ))) (σ₁ t, w₁) ∧
          HasFDerivAt Φ (D' : (ℂ × (Fin 2 → ℂ)) →L[ℂ] (ℂ × (Fin 2 → ℂ))) (σ₁ t, w₁') ∧
          (∀ σ ∈ 𝒰, ∀ (w w' : Fin 2 → ℂ),
            ((σ t, w) : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁) : ℂ × (Fin 2 → ℂ)) δ →
            ((σ t, w') : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁') : ℂ × (Fin 2 → ℂ)) δ →
            ∀ (hV : ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V)
              (hV' : ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V),
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV) f₂) =
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (u (σ t)).1).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV') f₂) →
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV) f₃) =
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (u (σ t)).1).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV') f₃) →
              (((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)) =
                (((e (u (σ t)).1).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)))))
    (hKCL :
      (∀ w : Fin 2 → ℂ, κ (σ₀ t) • w ∉ latt (u (σ₀ t)).1 →
        ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Metric.ball (σ₀ t) δ, ∀ w' : Fin 2 → ℂ,
          κ z • w' ∈ latt (u z).1 → δ ≤ ‖w' - w‖))
    (hRELSURJ :
      (∀ σ₁ ∈ 𝒰, σ₁ t ∈ Metric.ball (σ₀ t) ε → ∀ (w₁ : Fin 2 → ℂ) (ρ : ℝ), 0 < ρ →
        ∃ (V : 𝒰𝒜.1.A.Opens) (fs : Finset ↑(Γ(𝒰𝒜.1.A, V))) (ε₁ : ℝ)
          (h₁ : ⊤ ≤ (((e (u (σ₁ t)).1).symm ((κ (σ₁ t) • w₁ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ₁ t)).1).toAddSubgroup)).1 ≫ g (σ₁ t)) ⁻¹ᵁ V),
          0 < ε₁ ∧ ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε₁ →
            ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u (σ t)).1.f)
              (hP : ⊤ ≤ (P.1 ≫ g (σ t)) ⁻¹ᵁ V),
              (∀ φ ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P.1 ≫ g (σ t)).appLE V ⊤ hP) φ) -
                  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (u (σ₁ t)).1).symm ((κ (σ₁ t) • w₁ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ₁ t)).1).toAddSubgroup)).1 ≫ g (σ₁ t)).appLE V ⊤ h₁) φ)‖ < ε₁) →
              ∃ w ∈ Metric.ball w₁ ρ,
                e (u (σ t)).1 P = ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)))

    (ε' : ℝ) (v : Fin 4 → ℂ → (Fin 2 → ℂ)) (hε' : 0 < ε') (hε'ε : ε' ≤ ε)
    (hv : ∀ i : Fin 4, DifferentiableOn ℂ (v i) (Metric.ball (σ₀ t) ε'))
    (hbasis : ∀ z ∈ Metric.ball (σ₀ t) ε',
        (∀ i : Fin 4, κ z • v i z ∈ latt (u z).1) ∧
        ∀ x ∈ latt (u z).1, ∃! n : Fin 4 → ℤ, (∑ i, (n i : ℂ) • v i z) = (κ z)⁻¹ • x) :
    ∃ (ε'' : ℝ) (a₀ : Fin 4 → ℤ), 0 < ε'' ∧ ε'' ≤ ε' ∧

      (∀ z ∈ Metric.ball (σ₀ t) ε'',
        e (u z).1 (u z).2.P =
          ((κ z • (((m : ℂ)⁻¹) • ∑ i, (a₀ i : ℂ) • v i z) : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup)) := by sorry
