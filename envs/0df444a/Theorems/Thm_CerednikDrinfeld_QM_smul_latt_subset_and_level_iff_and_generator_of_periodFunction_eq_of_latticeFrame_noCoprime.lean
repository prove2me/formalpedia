-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_smul_latt_subset_and_level_iff_and_generator_of_periodFunction_eq_of_latticeFrame_noCoprime
-- name    : CerednikDrinfeld.QM.smul_latt_subset_and_level_iff_and_generator_of_periodFunction_eq_of_latticeFrame_noCoprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/eec6eb39-835e-50ef-a517-1d5a71d858a1
-- title:
--   Homothety of period lattices at equal τ
-- statement:
--   Fix two primes $q,q'$ with $q'\neq q$ and rationals $a,b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: either $a>0$ or $b>0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra exactly when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order (an order containing no strictly larger order), let $\iota:\mathbb{H}[\mathbb{Q},a,b]\to M_2(\mathbb{R})$ be an injective $\mathbb{Q}$-algebra map, and let $N\neq 0$ be squarefree with $q\nmid N$, $q'\nmid N$. Let $R\leq\Lambda$ be an Eichler order of level $N$, i.e. $R=\Lambda_1\cap\Lambda_2$ for maximal orders $\Lambda_1,\Lambda_2$ with relative index $N$ of $R$ in $\Lambda_1$.
--
--   The first group of hypotheses is a *complex uniformisation* of the category of fake elliptic curves over $\mathbb{C}$ for $(\Lambda,N)$ (abelian schemes over $\operatorname{Spec}\mathbb{C}$ with commutative relative group law, two-dimensional fibres, an action `act` of $\Lambda$ satisfying the additivity, multiplicativity and trace conditions of `FakeEllipticCurve`, and a level-$N$ structure `lev : C ⟶ A`). It consists of: a map $\mathrm{latt}$ assigning to each such $E$ a $\mathbb{Z}$-submodule $\mathrm{latt}(E)$ of $\mathbb{C}^2$; equivalences $e_E$ between the $\mathbb{C}$-points of $E$ (sections of `E.f` over $\mathrm{id}_{\operatorname{Spec}\mathbb{C}}$) and $\mathbb{C}^2/\mathrm{latt}(E)$; `hL1`, stating that $\mathrm{latt}(E)$ is the $\mathbb{Z}$-span of some $\mathbb{R}$-basis of $\mathbb{C}^2$ indexed by `Fin 4` and is stable under $v\mapsto \iota(x)v$ (the complexified matrix acting by `mulVec`) for all $x\in\Lambda$; `hE1`, that $e_E$ takes the relative group law to addition; `hE2`, that $e_E$ intertwines the action of $x\in\Lambda$ on points with $v\mapsto\iota(x)v$; `hH1`, that every morphism $\varphi:E.A\to E'.A$ over $\operatorname{Spec}\mathbb{C}$ which is compatible with the group laws on $T$-points for all $T$ and commutes with the $\Lambda$-actions is given by a scalar $c\in\mathbb{C}$ with $c\cdot\mathrm{latt}(E)\subseteq\mathrm{latt}(E')$ and $e_{E'}(\varphi\circ P)=[cv]$ whenever $e_E(P)=[v]$; `hH2`, the converse existence statement for each such scalar $c$; `hH3`, that a morphism over the base is determined by its effect on $\mathbb{C}$-points; `hAN`, that for every open $U\subseteq E.A$ and every $f\in\Gamma(E.A,U)$ the set of $v\in\mathbb{C}^2$ for which the point $e_E^{-1}[v]$ lands in $U$ is open and the value of $f$ at that point is given on it by a function $F:\mathbb{C}^2\to\mathbb{C}$ differentiable there; and `hCOV`, that near every $v_0\in\mathbb{C}^2$ two sections $f_1,f_2$ over some open $U$ give, on a ball of radius $\varepsilon>0$ about $v_0$ whose points lie in $U$, a map $F:\mathbb{C}^2\to\mathbb{C}^2$ having an invertible continuous linear Fréchet derivative $D$ at $v_0$.
--
--   The second group is *fine moduli data at full level $m$*: an integer $m\geq 3$, a scheme $M$ with a morphism $\pi_M:M\to\operatorname{Spec}\mathbb{C}$, a point assignment $\mathrm{ptF}$ sending, for each commutative ring $S$ and each $s:\operatorname{Spec}S\to\operatorname{Spec}\mathbb{C}$, a pair consisting of a fake elliptic curve over $S$ together with a `FullLevel` structure of level $m$ (a point $P$ killed by $m$ which generates the $m$-torsion of geometric fibres under $\Lambda$ and whose annihilator in $\Lambda$ is $m\Lambda$) to a point of $\pi_M$ over $s$; the hypothesis `hM : IsFineModuli Λ N m M πM ptF`, i.e. $\mathrm{ptF}$ is invariant under isomorphism, compatible with base change along ring maps and pullback of data, surjective and injective up to isomorphism; and `hsm`, that $\pi_M$ is smooth of relative dimension $1$.
--
--   The third group is an *algebraic chart with an analytic coordinate*: a finitely generated $\mathbb{C}$-algebra $Sc$ which is a domain, an open immersion $j:\operatorname{Spec}Sc\to M$ with `hj` saying that $j$ followed by $\pi_M$ is the structure morphism of $Sc$, an element $t\in Sc$, a $\mathbb{C}$-point $\sigma_0$ of $Sc$, a radius $r>0$ and a set $\mathcal{U}$ of $\mathbb{C}$-points containing $\sigma_0$ such that $\sigma\mapsto\sigma(t)$ is a bijection from $\mathcal{U}$ onto the ball of radius $r$ about $\sigma_0(t)$ (`hbij`), and such that for every $s\in Sc$ there is a function holomorphic on that ball computing $\sigma(s)$ from $\sigma(t)$ for all $\sigma\in\mathcal{U}$ (`hhol`).
--
--   The fourth group is a *holomorphic lattice frame over the $\varepsilon$-disc*: a radius $\varepsilon$ with $0<\varepsilon\leq r$, a family $z\mapsto u(z)$ of fake elliptic curves over $\mathbb{C}$ with full level $m$ structure, a scaling function $\kappa$, four functions $v_i:\mathbb{C}\to\mathbb{C}^2$, a set $T\subseteq(\mathrm{Fin}\,4\to\mathbb{Z})$ and a vector $a_0\in(\mathrm{Fin}\,4\to\mathbb{Z})$, subject to: `hκ`, $\kappa(z)\neq 0$ on the ball of radius $\varepsilon$ about $\sigma_0(t)$; `hPT`, for $\sigma\in\mathcal{U}$ with $\sigma(t)$ in that ball, every point of $\pi_M$ over $\mathrm{id}$ whose underlying morphism is $\operatorname{Spec}(\sigma)$ followed by $j$ equals $\mathrm{ptF}(u(\sigma(t)))$; `hBASIS`, for $z$ in the ball each $v_i(z)$ lies in $\kappa(z)\cdot\mathrm{latt}(u(z)_1)$ and every element of $\kappa(z)\cdot\mathrm{latt}(u(z)_1)$ is uniquely $\sum_i n_i v_i(z)$ with $n\in(\mathrm{Fin}\,4\to\mathbb{Z})$; `hLEVN`, for $z$ in the ball and $w\in\mathbb{C}^2$, there is a $\mathbb{C}$-point $P$ of $u(z)_1$ factoring through its level structure `lev` with $e_{u(z)_1}(P)=[w]$ if and only if $[w]=[\kappa(z)^{-1}N^{-1}\sum_i n_i v_i(z)]$ for some $n\in T$; and `hLEVM`, for $z$ in the ball the full-level generator $u(z)_2.P$ satisfies $e_{u(z)_1}(u(z)_2.P)=[\kappa(z)^{-1}m^{-1}\sum_i a_{0,i} v_i(z)]$.
--
--   The fifth group is the *quaternionic normalisation of the frame*: functions $\tau:\mathbb{C}\to\mathcal{H}$ into the upper half plane and $c:\mathbb{C}\to\mathbb{C}$, quaternions $y_i$ ($i\in\mathrm{Fin}\,4$), with `hc` asserting $c(z)\neq0$ on the $\varepsilon$-ball and `hper` asserting that for $z$ in that ball and each $i$ one has $c(z)\,v_i(z)=\iota(y_i)\binom{\tau(z)}{1}$, the complexified matrix $\iota(y_i)$ applied to $(\tau(z),1)$, as in `qmPeriodMap`.
--
--   Finally let $z,z'$ lie in the ball of radius $\varepsilon$ about $\sigma_0(t)$ with $\tau(z)=\tau(z')$, and put
--   $$H=\frac{c(z)\,\kappa(z)}{c(z')\,\kappa(z')}.$$
--   The conclusion is the conjunction of five assertions: (i) $H\neq0$; (ii) $H\cdot w\in\mathrm{latt}(u(z')_1)$ for every $w\in\mathrm{latt}(u(z)_1)$; (iii) $H^{-1}\cdot w\in\mathrm{latt}(u(z)_1)$ for every $w\in\mathrm{latt}(u(z')_1)$; (iv) for every $w\in\mathbb{C}^2$, there exists a $\mathbb{C}$-point $P$ of $u(z)_1$ factoring through the level structure of $u(z)_1$ with $e_{u(z)_1}(P)=[w]$ if and only if there exists a $\mathbb{C}$-point $P'$ of $u(z')_1$ factoring through the level structure of $u(z')_1$ with $e_{u(z')_1}(P')=[Hw]$; and (v) for every $w_0\in\mathbb{C}^2$, if $e_{u(z)_1}(u(z)_2.P)=[w_0]$ then $e_{u(z')_1}(u(z')_2.P)=[Hw_0]$, the classes being taken modulo $\mathrm{latt}(u(z)_1)$ and $\mathrm{latt}(u(z')_1)$ respectively.
--
--   This is the linear-algebra half of the injectivity of the period function on the local analytic chart of the fine moduli scheme of fake elliptic curves with full level $m$: equality of the normalised period point $\tau$ at two parameters forces the two period lattices, together with their level-$N$ points and their level-$m$ generators, to be carried onto one another by a single homothety $H$. It is used by [`CerednikDrinfeld.QM.IsFineModuli.injOn_periodFunction_of_latticeFrame_of_analytic_noCoprime`](thm.html#CerednikDrinfeld.QM.IsFineModuli.injOn_periodFunction_of_latticeFrame_of_analytic_noCoprime), where the homothety is converted into an isomorphism of fake elliptic curves with level structure and hence, by the fine moduli property, into equality of chart points. The hypothesis list imposes no coprimality between the fine level $m$ and $N q q'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_smul_latt_subset_and_level_iff_and_generator_of_periodFunction_eq_of_latticeFrame_noCoprime.lean

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

theorem CerednikDrinfeld.QM.smul_latt_subset_and_level_iff_and_generator_of_periodFunction_eq_of_latticeFrame_noCoprime
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
    (hper : ∀ z ∈ Metric.ball (σ₀ t) ε, ∀ i : Fin 4, c z • v i z = qmPeriodMap ι (τ z) (y i))
    (z z' : ℂ) (hz : z ∈ Metric.ball (σ₀ t) ε) (hz' : z' ∈ Metric.ball (σ₀ t) ε) (hτ : τ z = τ z') :
    let H : ℂ := (c z * κ z) / (c z' * κ z')
    H ≠ 0 ∧
    (∀ w ∈ latt (u z).1, H • w ∈ latt (u z').1) ∧
    (∀ w ∈ latt (u z').1, H⁻¹ • w ∈ latt (u z).1) ∧
    (∀ w : Fin 2 → ℂ,
      (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u z).1.f,
          FactorsThrough (u z).1.lev P ∧ e (u z).1 P = ((w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup)) ↔
      (∃ P' : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u z').1.f,
          FactorsThrough (u z').1.lev P' ∧ e (u z').1 P' = ((H • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z').1).toAddSubgroup))) ∧
    (∀ w₀ : Fin 2 → ℂ, e (u z).1 (u z).2.P = ((w₀ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup) →
      e (u z').1 (u z').2.P = ((H • w₀ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z').1).toAddSubgroup)) := by sorry
