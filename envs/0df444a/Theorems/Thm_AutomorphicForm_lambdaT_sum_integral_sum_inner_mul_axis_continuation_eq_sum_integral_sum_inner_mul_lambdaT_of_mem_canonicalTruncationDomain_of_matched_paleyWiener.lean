-- Prove2me | Theorems.Thm_AutomorphicForm_lambdaT_sum_integral_sum_inner_mul_axis_continuation_eq_sum_integral_sum_inner_mul_lambdaT_of_mem_canonicalTruncationDomain_of_matched_paleyWiener
-- name    : AutomorphicForm.lambdaT_sum_integral_sum_inner_mul_axis_continuation_eq_sum_integral_sum_inner_mul_lambdaT_of_mem_canonicalTruncationDomain_of_matched_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/68cd01e9-089a-50c8-b312-47dfcacc8051
-- title:
--   Truncation commutes with the Eisenstein wave-packet integral
-- statement:
--   Fix a number field $K$ and reals $\alpha,\beta$ with $0<\alpha$ and $\alpha<\beta$; all measures on $\mathrm{GL}_2$ of the adeles and on the adele ring are the Borel Haar measures `adelicGLHaar` and `adelicAddHaar`. Throughout, `pins` denotes the carrier data `productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: its measurable space and measure on $\mathrm{GL}_2(\mathbb{A}_K)$ are the Borel ones with Haar measure, its domain is the canonical truncation domain [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32), its central subgroup is the full unit group $\mathbb{A}_K^\times$, its level subgroups are $M\mapsto$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, its Hecke generators are `heckeGen (𝓞 K) K v`, and its measure on $\mathbb{A}_K$ is the additive Haar measure conditioned on the box `adelicBox K`.
--
--   A set $\Phi_K$ of adelic matrices is among the parameters; it occurs in no hypothesis and in neither side of the conclusion.
--
--   *Siegel covering data.* Reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}$, $d_{1K}<d_{2K}$, a finite set $T_K$ of adelic matrices, and the hypothesis `hcovK` that the union $\bigcup_{x\in T_K}(\cdot\,x)\big[\,$`centreCutSiegelSet K cK uK d₁K d₂K`$\,\big]$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo the centre, i.e. every $g$ can be written as $\gamma g z$ lying in that union with $\gamma\in\mathrm{GL}_2(K)$ and $z$ a central idele scalar.
--
--   *Central measure data.* A Haar measure $\nu_{Z_K}$ on $\mathbb{A}_K^\times$ and a set $\Omega_K$ which, by `hΩK`, is a fundamental domain for the subgroup of principal ideles (the range of $K^\times\to\mathbb{A}_K^\times$) acting on $\mathbb{A}_K^\times$ with respect to $\nu_{Z_K}$.
--
--   *Central character and level data.* A finite set $S_K$ of height-one primes of $\mathcal{O}_K$; a homomorphism $\xi_K$ from the full subgroup $\mathbb{A}_K^\times$ to $\mathbb{C}^\times$ which is continuous (`hξc`), trivial on principal ideles (`hξt`) and of absolute value $1$ at every idele (`hξu`); an ideal $N$ of $\mathcal{O}_K$ such that every prime dividing $N$ lies in $S_K$ (`hN`); and an archimedean type family $\mathrm{tys}_K$, that is, for each infinite place a finite list of representations of the local row-isometry group, cutting out the submodule `archCutSubmodule K tysK`.
--
--   *Modulus character.* $\alpha_m$ is the character $\mathbb{A}_K^\times\to\mathbb{R}^\times$ obtained from the distributive Haar character of $\mathbb{A}_K$, and $h\alpha_m$ asserts that all its values are positive.
--
--   *Cuspidal basis data.* A type $\iota$, functions $b_i:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ and Hecke eigensystems $\mathrm{cls}_i$ over $\mathbb{C}$ such that (`hb`) each $\mathrm{cls}_i$ is a cusp class in `cuspClasses K pins ξK N SK` and each $b_i$ lies in the intersection of the isotypic cusp submodule of $\mathrm{cls}_i$ with the archimedean cut submodule; $b$ is orthonormal for the inner product $\int_{\Phi_0} b_i\overline{b_j}$ over the canonical truncation domain (`hbn`, `hbo`); (`hbs`) for every cusp class $\pi$ the fibre $\{i\mid \mathrm{cls}_i=\pi\}$ is finite and the $\mathbb{C}$-span of its image under $b$ is exactly the $\pi$-isotypic cusp submodule intersected with the archimedean cut submodule; and (`hbc`) any $\varphi$ which is a smooth cuspidal automorphic function for `pins` and $\xi_K$, continuous, invariant under the level group `pins.U N`, of the prescribed archimedean type, and orthogonal to every $b_i$ over the truncation domain, vanishes almost everywhere there.
--
--   *Continuous-spectrum data.* A countable type $\iota_E$ with families of characters $\mu_e,\nu_e:\mathbb{A}_K^\times\to\mathbb{C}^\times$ which are unitary, trivial on $K^\times$, continuous, satisfy $\mu_e\nu_e=\xi_K$, and are pairwise distinguished already on the norm-one ideles [`NumberField.TateGlobal.normOneIdeles K`](def/NumberField_TateGlobalZeta.html#L16). For each $e$ an integer $n_E(e)$ and sections $\varphi_{e,j}(s)$, $j\in\mathrm{Fin}(n_E(e))$, $s\in\mathbb{C}$, subject to a group of hypotheses (summarised here, with their Lean names): each $\varphi_{e,j}(s)$ is an induced section for the pair `etaFst (μ e) αm hαm s`, `etaSnd (ν e) αm hαm s`, that is, transforms under the adelic Borel by $\mu_e|\cdot|^{s+1/2}$ on the first diagonal entry and $\nu_e|\cdot|^{-(s+1/2)}$ on the second (`_hφE`); it is archimedean $K$-finite (`_hφEK`), smooth for the finite adelic group (`_hφEf`), jointly continuous in $(s,g)$ (`_hφEjc`), entire in $s$ pointwise (`_hφEhol`), of uniformly finite-dimensional archimedean $K$-type at each infinite place (`_hφEKu`), flat along the maximal compact subgroup, $\varphi_{e,j}(s)(k)=\varphi_{e,j}(0)(k)$ (`_hφEflat`), invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` (`_hφElev`), of the prescribed archimedean type (`_hφEty`), orthonormal on the adelic maximal compact subgroup with respect to `maximalCompactHaar K` (`_hφEon`), and spanning: every continuous, archimedean $K$-finite, level-$N$-invariant section of the prescribed type on the unitary axis $s=it$ lies in the span of the $\varphi_{e,j}(it)$ (`_hφEspan`). The hypothesis `_hpairs` asserts that every pair of unitary idele class characters $(\mu',\nu')$, continuous with $\mu'\nu'=\xi_K$, admitting a nonzero such section at some point of the unitary axis, agrees with some $(\mu_e,\nu_e)$ on the norm-one ideles.
--
--   *Eisenstein continuations.* Sets $O_E(e,j)\subseteq\mathbb{C}$ and families $E_{e,j}$, $N_{e,j}$ with the hypothesis `_hEE`: $O_E(e,j)$ is open, preconnected and contains both the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$; for each $g$ the functions $s\mapsto E_{e,j}(s)(g)$ and $s\mapsto N_{e,j}(s)(g)$ are analytic on a neighbourhood of $O_E(e,j)$; both are continuous on $O_E(e,j)\times\mathrm{GL}_2(\mathbb{A}_K)$ jointly; and for $\mathrm{Re}\,s>1/2$ one has $E_{e,j}(s)(g)=\varphi_{e,j}(s)(g)+\sum_{\xi\in K}'\varphi_{e,j}(s)\big(w\,n(\xi)\,g\big)$ with $w$ the adelic Weyl element and $n(\xi)$ the unipotent of a principal adele, and $N_{e,j}(s)(g)$ equals the Weyl intertwining integral of $\varphi_{e,j}(s)$ at $g$ taken with respect to `adelicAddHaar`.
--
--   *Paley–Wiener datum.* A finite type $\iota_P$ with characters $\mu_{P,e},\nu_{P,e}$ which are unitary, trivial on $K^\times$, continuous, satisfy $\mu_{P,e}\nu_{P,e}=\xi_K$ on the central subgroup `pins.Z`, are permuted by a map $r_P$ exchanging $\mu_P$ and $\nu_P$, and are pairwise distinguished on the norm-one ideles; sections $\psi_{e}(s)$ which are induced sections for `etaFst (μP e) αm hαm s`, `etaSnd (νP e) αm hαm s`, jointly continuous, entire in $s$, archimedean $K$-finite, smooth for the finite adelic group, of uniformly finite-dimensional archimedean $K$-type (hypotheses `_hψf`, `_hψjc`, `_hψhol`, `_hψK`, `_hψsm`, `_hψKu`), level-$N$-invariant (`_hψlev`) and of the prescribed archimedean type (`_hψty`), together with the vertical-strip decay `_hψdec`: for each $e$, each $n\in\mathbb{N}$, each $\sigma_0$ and each compact $C$ there is an integrable bounded $m:\mathbb{R}\to\mathbb{R}$ with $(1+|t|)^n\|\psi_e(\sigma'+it)(g)\|\le m(t)$ for all $|\sigma'|\le\sigma_0$, $t\in\mathbb{R}$ and $g\in C$.
--
--   *Slab profile and matching.* A function $\psi$ which is a slab profile for the central subgroup `pins.Z` and $\xi_K$ (measurable, invariant under left translation by unipotents and by global Borel points, transforming by $\xi_K$ under the centre, bounded on each slab of bounded determinant idele norm, and supported in a band of adelic heights), with the representation `_hψrep`: for every $\sigma'\in\mathbb{R}$ and every $g$, $\psi(g)=\sum_{e\in\iota_P}(4\pi)^{-1}\int_{\mathbb{R}}\psi_e(\sigma'+it)(g)\,dt$; and matching data $\mathrm{em}:\iota_P\to\iota_E$, $\tau:\iota_P\to\mathbb{R}$ with (`_hem`) $\mu_{P,i}=\mu_{\mathrm{em}(i)}\cdot\|\cdot\|^{i\tau_i}$ and $\nu_{P,i}=\nu_{\mathrm{em}(i)}\cdot(\|\cdot\|^{i\tau_i})^{-1}$, where $\|\cdot\|^{i\tau}$ denotes [`NumberField.TateGlobal.normPowChar K τ`](def/NumberField_NormPowChar.html#L22).
--
--   *Conclusion.* Write $c_{i,j}(t)=\int \psi_i(it)(k)\,\overline{\varphi_{\mathrm{em}(i),j}\big(i(t+\tau_i)\big)(k)}\,d\,$`maximalCompactHaar K`$(k)$, the integral over the adelic maximal compact subgroup, and let $\Lambda^{T}$ denote [`AutomorphicForm.lambdaT`](def/AutomorphicForm_TruncationOperator.html#L48) taken with the measurable space `pins.nS` and measure `pins.ν` on $\mathbb{A}_K$, the unipotent family $x\mapsto$ [`AutomorphicForm.unipotentGL2 x`](def/AutomorphicForm_ConstantTerm.html#L17), the height function [`NumberField.AdelicHeight.adelicHeight K`](def/NumberField_AdelicHeight.html#L158) and the threshold $T$; thus $\Lambda^{T}\phi(g)=\phi(g)-\mathbf 1_{\{\,T<\mathrm{ht}(g)\,\}}(g)\cdot\mathrm{CT}\phi(g)$ with $\mathrm{CT}$ the constant term `constantTerm` along the unipotents computed for `pins.ν`. Then for every $R\in\mathbb{R}$ and every $x$ in [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32), with $T=\exp R$,
--   $$\Lambda^{T}\Big(g\mapsto\sum_{i\in\iota_P}\int_{\mathbb{R}}\sum_{j}c_{i,j}(t)\,E_{\mathrm{em}(i),j}\big(i(t+\tau_i)\big)(g)\,dt\Big)(x)=\sum_{i\in\iota_P}\int_{\mathbb{R}}\sum_{j}c_{i,j}(t)\,\Lambda^{T}\Big(E_{\mathrm{em}(i),j}\big(i(t+\tau_i)\big)\Big)(x)\,dt,$$
--   the inner sums being over $j\in\mathrm{Fin}\big(n_E(\mathrm{em}(i))\big)$. That is, the truncation of the Eisenstein wave packet attached to the Paley–Wiener datum coincides, on the canonical truncation domain, with the wave packet of the truncated Eisenstein series.
--
--   This is the interchange of the truncation operator with the wave-packet integral over the unitary axis, the step in the continuous part of the spectral decomposition which allows the truncated packet to be treated term by term. It is used in establishing square-integrability of the truncated packet on the canonical truncation domain, in [`AutomorphicForm.exists_forall_memLp_two_lambdaT_sum_integral_sum_inner_mul_axis_continuation_restrict_canonicalTruncationDomain_of_matched_paleyWiener`](thm.html#AutomorphicForm.exists_forall_memLp_two_lambdaT_sum_integral_sum_inner_mul_axis_continuation_restrict_canonicalTruncationDomain_of_matched_paleyWiener).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_lambdaT_sum_integral_sum_inner_mul_axis_continuation_eq_sum_integral_sum_inner_mul_lambdaT_of_mem_canonicalTruncationDomain_of_matched_paleyWiener.lean

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

theorem AutomorphicForm.lambdaT_sum_integral_sum_inner_mul_axis_continuation_eq_sum_integral_sum_inner_mul_lambdaT_of_mem_canonicalTruncationDomain_of_matched_paleyWiener
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
      (ιP : Type) [Fintype ιP]
      (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μP e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (νP e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μP e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (νP e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP e x : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιP)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP e (z : (AdeleRing (𝓞 K) K)ˣ) * νP e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP : ιP → ιP) (_hr : ∀ e, μP (rP e) = νP e ∧ νP (rP e) = μP e)
      (_hdist : ∀ e e' : ιP, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP e x ≠ μP e' x ∨ νP e x ≠ νP e' x)
      (ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite K (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth K (ψf e s))
      (_hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (em : ιP → ιE) (τ : ιP → ℝ)
      (_hem : ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹)
      (_hψlev : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf i s (g * u) = ψf i s g)
      (_hψty : ∀ i (s : ℂ), ψf i s ∈ archCutSubmodule K tysK),
    ∀ (R : ℝ), ∀ x ∈ AutomorphicForm.canonicalTruncationDomain K α β,
        @AutomorphicForm.lambdaT _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).nS _ _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν
          (fun n => AutomorphicForm.unipotentGL2 n) (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (fun g : AdelicGL2 (𝓞 K) K =>
            ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)), (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                ∂(maximalCompactHaar K)) * EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) x =
          ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)), (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                ∂(maximalCompactHaar K)) *
            @AutomorphicForm.lambdaT _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).nS _ _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν
          (fun n => AutomorphicForm.unipotentGL2 n) (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I)) x := by sorry
