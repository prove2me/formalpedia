-- Prove2me | Theorems.Thm_AutomorphicForm_analyticOnNhd_setIntegral_axis_continuation_mul_conj_cuspBasis
-- name    : AutomorphicForm.analyticOnNhd_setIntegral_axis_continuation_mul_conj_cuspBasis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/911062f7-8cc5-59dc-8426-00f071cc5d2f
-- title:
--   Holomorphy of the Eisenstein–cusp pairing on the truncation domain
-- statement:
--   Throughout, $K$ is a number field, $G = \mathrm{GL}_2(\mathbb{A}_K)$ is `AdelicGL2 (𝓞 K) K`, and $\mu_G$ denotes the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` on $G$ for the Borel $\sigma$-algebra `glBorel`. Two reals $\alpha < \beta$ with $0 < \alpha$ are fixed, and $\Phi_0 =$ `canonicalTruncationDomain K α β` is the canonically chosen truncation domain attached to the slab $[\alpha,\beta]$. A set $\Phi_K \subseteq G$ is among the binders but is constrained by no hypothesis and does not occur in the conclusion.
--
--   Siegel covering data. Reals $c_K, u_K, d_{1K}, d_{2K}$ with $0 < c_K$, $0 < d_{1K} < d_{2K}$ and a finite set $T_K \subseteq G$ are given, together with the hypothesis `hcovK` that the union $\bigcup_{x \in T_K} (\,\cdot\, x)\bigl[\mathrm{centreCutSiegelSet}\ K\ c_K\,u_K\,d_{1K}\,d_{2K}\bigr]$ covers $G$ modulo the centre in the sense of `CoversModCentre`: for every $g \in G$ there are $\gamma \in \mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g\,z$ (image of $\gamma$ under `globalPoints`, central scalar $z$) in that union. Here the centre-cut Siegel set consists of those $g$ whose finite component lies in `finiteIntegralGL2`, whose archimedean component at every infinite place $w$ has local height $\ge c_K$ and $x$-window square $\le u_K^2$, and whose archimedean determinant norm at every $w$ lies in $[d_{1K}, d_{2K}]$.
--
--   Central data. A Haar measure $\nu_{Z,K}$ on the idele group $\mathbb{A}_K^\times$ (with a measurable and Borel structure on $\mathbb{A}_K^\times$) and a set $\Omega_K \subseteq \mathbb{A}_K^\times$ which, by `hΩK`, is a fundamental domain for the action of the image of $K^\times$ in $\mathbb{A}_K^\times$ with respect to $\nu_{Z,K}$.
--
--   Character, level and type data. A finite set $S_K$ of finite places of $K$; a homomorphism $\xi_K$ from the full subgroup $\top \le \mathbb{A}_K^\times$ to $\mathbb{C}^\times$ which is continuous (`hξc`), trivial on the image of $K^\times$ (`hξt`) and of absolute value $1$ at every idele (`hξu`); an ideal $N \subseteq \mathcal{O}_K$ such that every place $v$ with $v \mid N$ lies in $S_K$ (`hN`); and an archimedean type family $\mathrm{tys}_K$, that is, for every infinite place $w$ a number $\mathrm{card}\,w$ of archimedean types `ArchRepAt` at $w$.
--
--   The character $\alpha_m : \mathbb{A}_K^\times \to \mathbb{R}^\times$ is the unit-group homomorphism obtained from the distributive Haar character (module) of $\mathbb{A}_K$ composed with $\mathbb{R}_{\ge 0} \to \mathbb{R}$, and $h_{\alpha m}$ asserts $\alpha_m(x) > 0$ for every $x$; the adele Borel structure is used throughout. For a character $\chi$ and $s \in \mathbb{C}$, `etaFst` $\chi$ is $\chi \cdot \alpha_m^{\,s + 1/2}$ and `etaSnd` $\chi$ is $\chi \cdot \alpha_m^{-(s+1/2)}$, the powers being taken by `cpowChar`.
--
--   The carrier data `pins` used below is `productionPinsOf K Φ₀ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: measure $\mu_G$ on $G$ with the Borel structure, domain $\Phi_0$, central subgroup $\top$, level subgroups $U(M) =$ `principalLevel` $M \sqcap$ `finiteAdelicGL2Subgroup`, Hecke generators `heckeGen v`, and, on $\mathbb{A}_K$, the additive Haar measure conditioned on the adelic box.
--
--   Cusp form basis data. A type $\iota$, functions $b : \iota \to (G \to \mathbb{C})$ and $\mathrm{cls} : \iota \to$ `HeckeEigensystem K ℂ` are given, subject to four groups of hypotheses. `hb`: for every $i$, $\mathrm{cls}\,i$ lies in `cuspClasses K pins ξK N SK` — its level is $N$, its Hecke data $a_v, b_v$ vanish for $v \in S_K$, and its isotypic cusp submodule is non-zero — and $b_i$ lies in the intersection of `isotypicCuspSubmodule K pins ξK N SK (cls i)` (the $\mathbb{C}$-span of the functions that are smooth cuspidal automorphic at `pins` with character $\xi_K$, continuous, right invariant under $U(N)$, Hecke eigenfunctions with eigenvalue $a_v$ at all $v \notin S_K$ and central eigenfunctions with eigenvalue $b_v$ there) with `archCutSubmodule K tysK` (the intersection over infinite places $w$ of the sum of the type submodules of the prescribed types at $w$). `hbn` and `hbo`: the family is orthonormal for the pairing $\int_{\Phi_0} b_i(g)\overline{b_j(g)}\,d\mu_G(g)$, equal to $1$ for $i = j$ and to $0$ for $i \ne j$. `hbs`: for every $\pi$ in `cuspClasses K pins ξK N SK` the set $\{i \mid \mathrm{cls}\,i = \pi\}$ is finite and the $\mathbb{C}$-span of its image under $b$ equals the intersection of the isotypic cusp submodule of $\pi$ with the archimedean cut submodule. `hbc`: completeness — every $\varphi : G \to \mathbb{C}$ that is smooth cuspidal automorphic at `pins` with character $\xi_K$, continuous, right invariant under $U(N)$, a member of the archimedean cut submodule, and orthogonal over $\Phi_0$ to every $b_i$, vanishes almost everywhere for $\mu_G$ restricted to $\Phi_0$.
--
--   Eisenstein data. A countable type $\iota_E$ indexes pairs of characters $\mu_e, \nu_e : \mathbb{A}_K^\times \to \mathbb{C}^\times$, subject to a group of hypotheses: each $\mu_e$, $\nu_e$ is unitary (`IsUnitaryChar`), trivial on $K^\times$ (`IsIdeleClassChar`) and continuous, $\mu_e(z)\nu_e(z) = \xi_K(z)$ for all ideles $z$, and distinct indices are separated on the norm-one ideles (the kernel of the module character), `_hdist`. For each $e$ a natural number $n_E(e)$ and a family $\varphi_{e,j} : \mathbb{C} \to G \to \mathbb{C}$, $j \in \mathrm{Fin}(n_E(e))$, is given, subject to eleven clauses: each $\varphi_{e,j}(s)$ is an induced section for the pair $(\,$`etaFst` $\mu_e$ at $s$, `etaSnd` $\nu_e$ at $s)$, i.e. transforms under the adelic Borel subgroup by the product of those characters evaluated on the two diagonal entries; is archimedean $K$-finite and $K_f$-smooth; the family is jointly continuous in $(s,g)$ and holomorphic in $s$ for each $g$; the right translates under `archRowIsometrySubgroup K w` all lie in one finite-dimensional space, uniformly in $s$ and $g$, for each infinite place $w$; $\varphi_{e,j}(s)$ agrees with $\varphi_{e,j}(0)$ on `adelicMaximalCompact K`; $\varphi_{e,j}(s)$ is right invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` and lies in the archimedean cut submodule; the restrictions $\varphi_{e,j}(0)$ to the maximal compact are orthonormal for `maximalCompactHaar K`; on the unitary axis $s = it$ ($t \in \mathbb{R}$) every continuous, archimedean $K$-finite, level-$N$-invariant induced section of the correct type lies in the $\mathbb{C}$-span of the $\varphi_{e,j}(it)$ (`_hφEspan`); and `_hpairs` requires that every pair $(\mu',\nu')$ of continuous unitary idele class characters with product $\xi_K$ admitting a non-zero such section at some $s = it$ agrees with some $(\mu_e,\nu_e)$ on the norm-one ideles.
--
--   Continuation data. Sets $O_{e,j} \subseteq \mathbb{C}$ and families $E_{e,j}, N_{e,j} : \mathbb{C} \to G \to \mathbb{C}$ are given, subject to the nine clauses of `_hEE`: $O_{e,j}$ is open and preconnected and contains both the imaginary axis $\{\mathrm{Re}\,s = 0\}$ and the half-plane $\{\mathrm{Re}\,s > 1/2\}$; for each $g$, the functions $s \mapsto E_{e,j}(s)(g)$ and $s \mapsto N_{e,j}(s)(g)$ are analytic on a neighbourhood of every point of $O_{e,j}$; both are jointly continuous on $O_{e,j} \times G$; for $\mathrm{Re}\,s > 1/2$ one has $E_{e,j}(s)(g) = \varphi_{e,j}(s)(g) + \sum_{\xi \in K}^{\prime} \varphi_{e,j}(s)\bigl(w\,u(\xi)\,g\bigr)$, with $w =$ `adelicWeyl` and $u(\xi) =$ `unipotentGL2` of the image of $\xi$; and, in the same region, $N_{e,j}(s)(g)$ equals the Weyl intertwining integral `weylIntertwiningIntegral` of $\varphi_{e,j}(s)$ at $g$ for the adelic additive Haar measure.
--
--   Conclusion. For every $e \in \iota_E$, every $j \in \mathrm{Fin}(n_E(e))$ and every $i \in \iota$, the function
--   $$s \longmapsto \int_{\Phi_0} E_{e,j}(s)(g)\,\overline{b_i(g)}\,d\mu_G(g)$$
--   is analytic on a neighbourhood of each point of $O_{e,j}$, i.e. satisfies `AnalyticOnNhd ℂ · (OE e j)`.
--
--   This is the holomorphy half of the statement that continued Eisenstein series are orthogonal to cusp forms: the pairing of the analytically continued Eisenstein series $E_{e,j}$ with a member $b_i$ of the orthonormal basis of level-$N$, fixed-type cusp forms, taken over the canonical truncation domain, is a holomorphic function of $s$ on the whole domain of continuation, not merely on the half-plane of absolute convergence. It is used by [`AutomorphicForm.setIntegral_axis_continuation_mul_conj_cuspBasis_eq_zero_of_mem`](thm.html#AutomorphicForm.setIntegral_axis_continuation_mul_conj_cuspBasis_eq_zero_of_mem), where the vanishing of the pairing in the convergence region is propagated to $O_{e,j}$ by analytic continuation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_analyticOnNhd_setIntegral_axis_continuation_mul_conj_cuspBasis.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.analyticOnNhd_setIntegral_axis_continuation_mul_conj_cuspBasis
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
      (hb : ∀ i, cls i ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK ∧
          b i ∈ isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK (cls i) ⊓ archCutSubmodule K tysK)
      (hbn : ∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 1)
      (hbo : ∀ i j, i ≠ j → ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b j g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (hbs : ∀ π ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK,
          {i | cls i = π}.Finite ∧
          Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK)
      (hbc : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
          IsSmoothCuspAutomorphicFnAt K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ →
          Continuous φ →
          (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, φ (g * u) = φ g) →
          φ ∈ archCutSubmodule K tysK →
          (∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              φ g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) →
          φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)] 0)
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ), μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩)
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles K,
        μ e z ≠ μ e' z ∨ ν e z ≠ ν e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite K (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth K (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE e j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact K),
        φE e j s (k : AdelicGL2 (𝓞 K) K) = φE e j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (ν e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (_hpairs : ∀ (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 K) K μ' → IsUnitaryChar (𝓞 K) K ν' →
        IsIdeleClassChar (𝓞 K) K μ' → IsIdeleClassChar (𝓞 K) K ν' →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 K) K)ˣ, μ' z * ν' z = ξK ⟨z, Subgroup.mem_top z⟩) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z = μ' z ∧ ν e z = ν' z)
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE e j s g = φE e j s g + ∑' ξ : K, φE e j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g))
      (e : ιE) (j : Fin (nE e)) (i : ι),
    AnalyticOnNhd ℂ (fun s : ℂ => ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        EE e j s g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) (OE e j) := by sorry
