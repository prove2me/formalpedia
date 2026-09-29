-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_smul_latt_subset_and_level_iff_and_generator_of_periodFunction_eq_of_latticeFrame
-- name    : CerednikDrinfeld.QM.smul_latt_subset_and_level_iff_and_generator_of_periodFunction_eq_of_latticeFrame
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/60b0d17e-c7ad-529e-9987-3fe713959846
-- title:
--   Homothety of period lattices from equal quaternionic periods
-- statement:
--   Fix rationals $a,b$ and primes $q,q'$ with $q'\neq q$, and let $\mathbb H = \mathbb H[\mathbb Q,a,b]$ be the associated quaternion algebra. The hypothesis `hB` is `IsIndefiniteRamifiedExactlyAt a b q q'`: $0<a$ or $0<b$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the completion $\mathbb H\otimes_{\mathbb Q}\mathbb Q_v$ is a division algebra (every nonzero element is a unit) exactly when $q\in v$ or $q'\in v$. Further data: a $\mathbb Z$-submodule $\Lambda\subseteq\mathbb H$ which is an order maximal among the orders containing it (`hΛ`); an injective $\mathbb Q$-algebra map $\iota:\mathbb H\to M_2(\mathbb R)$; a nonzero squarefree integer $N$ divisible by neither $q$ nor $q'$; and a $\mathbb Z$-submodule $R\subseteq\Lambda$ which is an Eichler order of level $N$, i.e. $R=\Lambda_1\cap\Lambda_2$ for maximal orders $\Lambda_1,\Lambda_2$ with the relative index of $R$ in $\Lambda_1$ equal to $N$.
--
--   The analytic uniformisation data consist of a map $\mathrm{latt}$ assigning to every fake elliptic curve $E$ over $\mathbb C$ (an object of `FakeEllipticCurve Λ N ℂ`) a $\mathbb Z$-submodule $\mathrm{latt}(E)\subseteq\mathbb C^2$, and of bijections $e_E$ between the $\mathbb C$-points of $E$ (morphisms $\mathrm{Spec}\,\mathbb C\to E.A$ composing with $E.f$ to the identity) and $\mathbb C^2/\mathrm{latt}(E)$. These are subject to: `hL1`, that $\mathrm{latt}(E)$ is the $\mathbb Z$-span of an $\mathbb R$-basis of $\mathbb C^2$ indexed by $\mathrm{Fin}\,4$ and is stable under $v\mapsto \iota(x)_{\mathbb C}\,v$ for $x\in\Lambda$; `hE1`, that $e_E$ is additive for the relative group law $E.L$; `hE2`, that $e_E$ intertwines the action of $x\in\Lambda$ on points (push-forward along $E.\mathrm{act}\,x$) with multiplication by the complexified matrix $\iota(x)_{\mathbb C}$; `hH1`, that every morphism $\varphi:E.A\to E'.A$ over $\mathrm{Spec}\,\mathbb C$ which is compatible with the group laws on all $T$-points and commutes with the $\Lambda$-actions is induced by some scalar $c\in\mathbb C$ with $c\cdot\mathrm{latt}(E)\subseteq\mathrm{latt}(E')$, in the sense that $e_{E'}$ of the image point is the class of $c\,v$ whenever $e_E$ of the point is the class of $v$; `hH2`, the converse, that every $c$ with $c\cdot\mathrm{latt}(E)\subseteq\mathrm{latt}(E')$ comes from such a $\varphi$; `hH3`, that two morphisms over the base inducing the same map on $\mathbb C$-points coincide; `hAN`, that for every $E$, open $U\subseteq E.A$ and $f\in\Gamma(E.A,U)$ the set of $v\in\mathbb C^2$ for which the point $e_E^{-1}[v]$ lands in $U$ is open and the function $v\mapsto f$ evaluated at that point (via the canonical isomorphism $\Gamma(\mathrm{Spec}\,\mathbb C)\cong\mathbb C$) is the restriction of a function differentiable on that set; and `hCOV`, that for every $E$ and $v_0\in\mathbb C^2$ there are an open $U$, two sections $f_1,f_2\in\Gamma(E.A,U)$, a radius $\varepsilon>0$ with all points $e_E^{-1}[v]$, $v\in B(v_0,\varepsilon)$, landing in $U$, a continuous $\mathbb C$-linear automorphism $D$ of $\mathbb C^2$ and a map $F:\mathbb C^2\to\mathbb C^2$ given on that ball by the pair of values of $f_1,f_2$ at $e_E^{-1}[v]$ and having Fréchet derivative $D$ at $v_0$.
--
--   The moduli data consist of an integer $m\geq 3$ coprime to $Nqq'$, a scheme $M$ with a morphism $\pi_M:M\to\mathrm{Spec}\,\mathbb C$, and a classifying map $\mathrm{ptF}$ sending each commutative ring $S$, each $s:\mathrm{Spec}\,S\to\mathrm{Spec}\,\mathbb C$ and each fake elliptic curve over $S$ with a full level-$m$ structure to a point of $M$ over $s$; `hM` asserts that these make $M$ a fine moduli scheme (the classifying map is constant on isomorphism classes, compatible with base change, surjective on points over every base, and injective up to isomorphism), and `hsm` that $\pi_M$ is smooth of relative dimension $1$.
--
--   The algebraic chart consists of a finite-type $\mathbb C$-algebra $S_c$ which is a domain, an open immersion $j:\mathrm{Spec}\,S_c\to M$ with $j$ followed by $\pi_M$ equal to the structure morphism of $S_c$ over $\mathbb C$, an element $t\in S_c$, a $\mathbb C$-point $\sigma_0$, a radius $r>0$ and a set $\mathcal U$ of $\mathbb C$-points of $S_c$ containing $\sigma_0$ such that $\sigma\mapsto\sigma t$ is a bijection from $\mathcal U$ onto the ball $B(\sigma_0t,r)$ (`hbij`) and such that every $s\in S_c$ is a holomorphic function of the coordinate $t$: there is $F$ differentiable on $B(\sigma_0t,r)$ with $\sigma s=F(\sigma t)$ for all $\sigma\in\mathcal U$ (`hhol`).
--
--   The lattice frame over the disc consists of $0<\varepsilon\leq r$, a family $z\mapsto u(z)$ of fake elliptic curves over $\mathbb C$ with full level-$m$ structure, a scaling function $\kappa$, four vector-valued functions $v_1,\dots,v_4$, a set $T$ of integral $4$-tuples and a fixed $4$-tuple $a_0$, subject to: `hκ`, $\kappa(z)\neq 0$ on $B(\sigma_0t,\varepsilon)$; `hPT`, that for $\sigma\in\mathcal U$ with $\sigma t$ in that ball, $u(\sigma t)$ is classified by the point $\mathrm{Spec}\,\sigma$ followed by $j$; `hBASIS`, that for $z$ in the ball each $v_i(z)$ lies in $\kappa(z)\cdot\mathrm{latt}(u(z).1)$ and every element of $\kappa(z)\cdot\mathrm{latt}(u(z).1)$ has a unique expression $\sum_i n_i v_i(z)$ with $n\in\mathbb Z^4$; `hLEVN`, that for $z$ in the ball a class $[w]$ is the $e$-image of a point of $u(z).1$ factoring through the level morphism $\mathrm{lev}$ of that curve if and only if $[w]=[\kappa(z)^{-1}N^{-1}\sum_i n_iv_i(z)]$ for some $n\in T$; and `hLEVM`, that the level-$m$ generator $u(z).2.P$ has $e$-image $[\kappa(z)^{-1}m^{-1}\sum_i a_{0,i}v_i(z)]$.
--
--   Finally there are functions $\tau$ into the upper half-plane and $c$ with $c(z)\neq 0$ on the ball (`hc`), and quaternions $y_1,\dots,y_4\in\mathbb H$, normalised by `hper`: for $z$ in the ball and each $i$, $c(z)\,v_i(z)=\iota(y_i)_{\mathbb C}\binom{\tau(z)}{1}$, the value of `qmPeriodMap ι (τ z)` at $y_i$.
--
--   Under these hypotheses, for any $z,z'$ in $B(\sigma_0t,\varepsilon)$ with $\tau(z)=\tau(z')$, putting
--   $$H=\frac{c(z)\,\kappa(z)}{c(z')\,\kappa(z')},$$
--   the following five assertions hold: $H\neq 0$; $H\cdot w\in\mathrm{latt}(u(z').1)$ for every $w\in\mathrm{latt}(u(z).1)$; $H^{-1}\cdot w\in\mathrm{latt}(u(z).1)$ for every $w\in\mathrm{latt}(u(z').1)$; for every $w\in\mathbb C^2$, there is a point $P$ of $u(z).1$ factoring through $u(z).1.\mathrm{lev}$ with $e_{u(z).1}(P)$ equal to the class of $w$ if and only if there is a point $P'$ of $u(z').1$ factoring through $u(z').1.\mathrm{lev}$ with $e_{u(z').1}(P')$ equal to the class of $H\,w$; and for every $w_0\in\mathbb C^2$, if $e_{u(z).1}$ of the level-$m$ generator $u(z).2.P$ is the class of $w_0$, then $e_{u(z').1}$ of the level-$m$ generator $u(z').2.P$ is the class of $H\,w_0$.
--
--   This is the lattice-theoretic step in the proof that the period map of a family of fake elliptic curves with full level structure is injective on a disc: equality of the upper-half-plane parameter at two points of the chart forces the two period lattices, together with their level-$N$ points and level-$m$ generators, to be related by a single homothety $H$. It is used by [`CerednikDrinfeld.QM.IsFineModuli.injOn_periodFunction_of_latticeFrame_of_analytic`](thm.html#CerednikDrinfeld.QM.IsFineModuli.injOn_periodFunction_of_latticeFrame_of_analytic), whose binder block it shares.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_smul_latt_subset_and_level_iff_and_generator_of_periodFunction_eq_of_latticeFrame.lean

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

theorem CerednikDrinfeld.QM.smul_latt_subset_and_level_iff_and_generator_of_periodFunction_eq_of_latticeFrame
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
