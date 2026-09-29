-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_const_level_frameCoords_of_uniformization_family_of_smooth
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_const_level_frameCoords_of_uniformization_family_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/e8b4dc6e-4426-5ebb-8454-7f3741d3662e
-- title:
--   Level-N points have locally constant frame coordinates
-- statement:
--   Fix primes $q,q'$ with $q'\neq q$ and rationals $a,b$, and assume `hB`, i.e. `IsIndefiniteRamifiedExactlyAt a b q q'`: either $a>0$ or $b>0$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all its nonzero elements invertible exactly when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is a maximal order (`hΛ`: an order, maximal among orders under inclusion), let $\iota:\mathbb{H}[\mathbb{Q},a,b]\to M_2(\mathbb{R})$ be an injective $\mathbb{Q}$-algebra map (`hι`), let $N\geq 1$ be squarefree and divisible by neither $q$ nor $q'$ (`hqN`, `hq'N`, `hN`), and let $R\subseteq\Lambda$ be an Eichler order of level $N$ (`hR`: $R=\Lambda_1\cap\Lambda_2$ for maximal orders $\Lambda_i$, with relative index $N$ of $R$ in $\Lambda_1$).
--
--   The complex uniformisation data are: a map $E\mapsto \mathrm{latt}\,E$ assigning to each fake elliptic curve $E$ of level $N$ for $\Lambda$ over $\mathbb{C}$ a $\mathbb{Z}$-submodule of $\mathbb{C}^2$, and bijections $e_E$ between the $\mathbb{C}$-points of $E$ (sections $\varphi$ of $E.f$ with $\varphi\circ\mathrm{id}_{\operatorname{Spec}\mathbb{C}}$ the identity, i.e. elements of `SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f`) and the quotient group $\mathbb{C}^2/\mathrm{latt}\,E$. These are subject to the following groups of hypotheses, each of which is required for all $E,E'$ as displayed in the Lean text: `hL1`, that $\mathrm{latt}\,E$ is the $\mathbb{Z}$-span of (the range of) an $\mathbb{R}$-basis of $\mathbb{C}^2$ indexed by `Fin 4` and is stable under $v\mapsto \iota(x)_{\mathbb{C}}\,v$ for all $x\in\Lambda$; `hE1`, that $e_E$ carries the relative group law $E.L$ on $\mathbb{C}$-points to addition; `hE2`, that $e_E$ intertwines the action $E.\mathrm{act}\,x$ of $x\in\Lambda$ with multiplication by the complexification of $\iota(x)$ on representatives; `hH1`, that every morphism $\varphi:E.A\to E'.A$ over $\operatorname{Spec}\mathbb{C}$ which is a homomorphism for the group laws on points over every test scheme and commutes with the $\Lambda$-actions is given by a scalar $c\in\mathbb{C}$ with $c\cdot\mathrm{latt}\,E\subseteq\mathrm{latt}\,E'$, compatibly with $e$; `hH2`, the converse existence statement for each such scalar $c$; `hH3`, rigidity — two morphisms over $\operatorname{Spec}\mathbb{C}$ agreeing on $\mathbb{C}$-points are equal; `hAN`, analyticity of the uniformisation — for each open $U\subseteq E.A$ and $f\in\Gamma(E.A,U)$ the set of $v\in\mathbb{C}^2$ whose point $e_E^{-1}[v]$ factors through $U$ is open and the pullback of $f$ along $e_E^{-1}[v]$ is a holomorphic function of $v$ there; `hCOV`, existence of local holomorphic charts — for each $E$ and each $v_0\in\mathbb{C}^2$ there are an open $U$, two sections $f_1,f_2\in\Gamma(E.A,U)$, a radius $\varepsilon>0$ with the whole ball $B(v_0,\varepsilon)$ mapping into $U$, a map $F:\mathbb{C}^2\to\mathbb{C}^2$ given on that ball by the pair of values of $f_1,f_2$ at $e_E^{-1}[v]$, and a continuous linear isomorphism $D$ of $\mathbb{C}^2$ with $F$ differentiable at $v_0$ with derivative $D$.
--
--   The base of the family is a finite-type smooth $\mathbb{C}$-algebra $Sc$ which is a domain whose module of Kähler differentials has rank $1$ over $Sc$ (`hSc`, `hΩ`), together with $t\in Sc$, a $\mathbb{C}$-point $\sigma_0$ of $Sc$, a radius $r>0$, and a set $\mathcal{U}$ of $\mathbb{C}$-points with $\sigma_0\in\mathcal{U}$ such that $\sigma\mapsto\sigma(t)$ is a bijection of $\mathcal{U}$ onto the ball $B(\sigma_0(t),r)$ (`hbij`) and every $s\in Sc$ is, on $\mathcal{U}$, the value at $\sigma(t)$ of a function holomorphic on that ball (`hhol`). Over this base sit $m\in\mathbb{N}$ and an object $\mathcal{UA}$ of `FakeEllipticCurve.WithFullLevel Λ N m Sc`, i.e. a fake elliptic curve of level $N$ over $Sc$ together with a full level-$m$ structure (an $m$-torsion point $P$ whose geometric specialisations generate the $m$-torsion under $\Lambda$ and whose annihilator in $\Lambda$ is $m\Lambda$). The fibres are presented by a family $z\mapsto u(z)$ of objects of `FakeEllipticCurve.WithFullLevel Λ N m ℂ` and morphisms $g(z):(u\,z).1.A\to\mathcal{UA}.1.A$, with `hg` asserting for each $\sigma\in\mathcal{U}$ that the square formed by $g(\sigma t)$, $(u(\sigma t)).1.f$, $\mathcal{UA}.1.f$ and $\operatorname{Spec}\sigma$ is a pullback, that $g(\sigma t)$ is compatible with the group laws on $\mathbb{C}$-points and commutes with the $\Lambda$-actions, that the image under $g(\sigma t)$ of any $\mathbb{C}$-point of $u(\sigma t)$ factoring through the level scheme $(u(\sigma t)).1.\mathrm{lev}$ factors through $\mathcal{UA}.1.\mathrm{lev}$, and that $g(\sigma t)$ carries the full level-$m$ point of $u(\sigma t)$ to the base change of that of $\mathcal{UA}$.
--
--   Finally there are a radius $\varepsilon$ with $0<\varepsilon\leq r$ and a scaling function $\kappa:\mathbb{C}\to\mathbb{C}$ nowhere zero on $B(\sigma_0(t),\varepsilon)$ (`hκ`), subject to four groups of conditions relating the family to the uniformisations through the points $e_{u(\sigma t)}^{-1}[\kappa(\sigma t)\,w]$ followed by $g(\sigma t)$ (contents summarised here): `hRELAN`, relative analyticity — for each open $V\subseteq\mathcal{UA}.1.A$ and each $f\in\Gamma(\mathcal{UA}.1.A,V)$ the set of pairs $(z,w)$ with $z\in B(\sigma_0(t),\varepsilon)$ of the form $z=\sigma(t)$, $\sigma\in\mathcal{U}$, and with the above composite landing in $V$ is open, and the pullback of $f$ is given on it by a function of $(z,w)$ holomorphic there; `hRELCOV`, relative charts together with separation — for $\sigma_1\in\mathcal{U}$ with $\sigma_1(t)\in B(\sigma_0(t),\varepsilon)$ and $w_1,w_1'$ giving the same composite, there are an open $V$, sections $f_2,f_3$, a radius $\delta>0$, continuous linear isomorphisms $D,D'$ of $\mathbb{C}\times\mathbb{C}^2$ and a map $\Phi$ given on the two $\delta$-balls around $(\sigma_1 t,w_1)$ and $(\sigma_1 t,w_1')$ by $(z,w)\mapsto(z,(f_2,f_3)$-values$)$, with both balls consisting of admissible pairs over $V$, with $\Phi$ differentiable at the two centres with derivatives $D$ and $D'$, and with the property that points of the two balls over the same $\sigma$ agreeing on $f_2$ and on $f_3$ give the same composite; `hKCL`, local discreteness — if $\kappa(\sigma_0 t)\,w\notin\mathrm{latt}(u(\sigma_0 t))$ then some $\delta>0$ satisfies $\lVert w'-w\rVert\geq\delta$ for all $z\in B(\sigma_0(t),\delta)$ and all $w'$ with $\kappa(z)\,w'\in\mathrm{latt}(u\,z)$; and `hRELSURJ`, relative surjectivity — for $\sigma_1\in\mathcal{U}$ with $\sigma_1(t)\in B(\sigma_0(t),\varepsilon)$, any $w_1$ and any $\rho>0$, there are an open $V$ containing the image of the point attached to $(\sigma_1 t,w_1)$, a finite set of sections of $V$, and $\varepsilon_1>0$ such that every $\mathbb{C}$-point $P$ of $u(\sigma t)$, for $\sigma\in\mathcal{U}$ with $\sigma(t)$ within $\varepsilon_1$ of $\sigma_1(t)$, whose image lands in $V$ and whose values on those sections are within $\varepsilon_1$ of those of the reference point, satisfies $e_{u(\sigma t)}P=[\kappa(\sigma t)\,w]$ for some $w\in B(w_1,\rho)$.
--
--   The frame is given by $\varepsilon'$ with $0<\varepsilon'\leq\varepsilon$ and four maps $v_0,\dots,v_3:\mathbb{C}\to\mathbb{C}^2$, holomorphic on $B(\sigma_0(t),\varepsilon')$ (`hv`), such that for every $z$ in that ball (`hbasis`) each $\kappa(z)\,v_i(z)$ lies in $\mathrm{latt}(u\,z)$ and every $x\in\mathrm{latt}(u\,z)$ has a unique expression $\kappa(z)^{-1}x=\sum_i n_i\,v_i(z)$ with $n\in\mathbb{Z}^{4}$.
--
--   Under these hypotheses there exist a radius $\varepsilon''$ and a set $T$ of integer vectors $n:\mathrm{Fin}\,4\to\mathbb{Z}$ such that $0<\varepsilon''$, $\varepsilon''\leq\varepsilon'$, and for every $z\in B(\sigma_0(t),\varepsilon'')$ and every $w\in\mathbb{C}^2$ the following are equivalent: there is a $\mathbb{C}$-point $P$ of $u(z)$ which factors through the level scheme, i.e. $P=P_0\circ(u\,z).1.\mathrm{lev}$ for some $P_0:\operatorname{Spec}\mathbb{C}\to(u\,z).1.C$, with $e_{(u\,z).1}P=[w]$ in $\mathbb{C}^2/\mathrm{latt}((u\,z).1)$; and there is $n\in T$ with
--   $$[w]=\Bigl[\kappa(z)\cdot N^{-1}\sum_i n_i\,v_i(z)\Bigr]\quad\text{in }\mathbb{C}^2/\mathrm{latt}((u\,z).1).$$
--   Thus the integer coordinate vectors describing the level-$N$ points in the holomorphic frame $\kappa(z)v_i(z)$ may be taken independent of $z$ near $\sigma_0(t)$.
--
--   This is the level-structure clause in the analysis of a holomorphic family of complex uniformisations of fake elliptic curves of level $N$ over a smooth affine curve: it records that, after shrinking the parameter disc, the level-$N$ points are cut out in the holomorphic frame $\kappa(z)v_i(z)$ by a fixed finite set of integer coordinate vectors, so the discrete datum does not vary with the parameter. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_const_frameCoords_of_uniformization_family_of_smooth`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_const_frameCoords_of_uniformization_family_of_smooth), which assembles this with the corresponding constancy statements for the lattice and for the full level-$m$ point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_const_level_frameCoords_of_uniformization_family_of_smooth.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_const_level_frameCoords_of_uniformization_family_of_smooth
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
    ∃ (ε'' : ℝ) (T : Set (Fin 4 → ℤ)), 0 < ε'' ∧ ε'' ≤ ε' ∧

      (∀ z ∈ Metric.ball (σ₀ t) ε'', ∀ w : Fin 2 → ℂ,
        (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u z).1.f,
            FactorsThrough (u z).1.lev P ∧ e (u z).1 P = (w : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup)) ↔
          ∃ n ∈ T, (w : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup) =
            ((κ z • (((N : ℂ)⁻¹) • ∑ i, (n i : ℂ) • v i z) : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup)) := by sorry
