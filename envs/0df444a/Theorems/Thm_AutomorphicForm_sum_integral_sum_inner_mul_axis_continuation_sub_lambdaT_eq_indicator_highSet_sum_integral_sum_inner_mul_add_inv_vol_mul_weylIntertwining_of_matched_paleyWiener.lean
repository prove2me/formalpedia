-- Prove2me | Theorems.Thm_AutomorphicForm_sum_integral_sum_inner_mul_axis_continuation_sub_lambdaT_eq_indicator_highSet_sum_integral_sum_inner_mul_add_inv_vol_mul_weylIntertwining_of_matched_paleyWiener
-- name    : AutomorphicForm.sum_integral_sum_inner_mul_axis_continuation_sub_lambdaT_eq_indicator_highSet_sum_integral_sum_inner_mul_add_inv_vol_mul_weylIntertwining_of_matched_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/9ec25f5e-4734-5374-bd8d-71bd965b3ddc
-- title:
--   Truncation of an Eisenstein wave packet on the unitary axis
-- statement:
--   Throughout, $K$ is a number field and $\alpha,\beta$ are reals with $0<\alpha$ and $\alpha<\beta$; $\Phi_0 :=$ [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) is the truncation domain extracted from the canonical truncation datum for the slab $(\alpha,\beta)$, and all integrals over $\Phi_0$ are taken for the adelic Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` on $\mathrm{GL}_2$ of the adeles. The carrier data used throughout is
--   $$\mathrm{pins} := \mathtt{productionPinsOf}\ K\ \Phi_0\ \bigl(M \mapsto \mathtt{principalLevel}\,(\mathcal O_K)\,K\,M \sqcap \mathtt{finiteAdelicGL2Subgroup}\,K\bigr)\ \bigl(v \mapsto \mathtt{heckeGen}\,(\mathcal O_K)\,K\,v\bigr)\ (\mathtt{adelicBox}\,K),$$
--   whose fields are: the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb A_K)$, the domain $\Phi_0$, the central subgroup $Z=\top\le \mathbb A_K^\times$, the level subgroups $U(M)=\mathtt{principalLevel}(M)\sqcap$ (kernel of the archimedean projection), the Hecke generators at finite places, the Borel structure on $\mathbb A_K$, and the measure $\nu =$ `adelicAddHaar` conditioned on the adelic box $\mathtt{adelicBox}\,K=\{x : x_\infty \in \mathtt{infiniteBox}\,K,\ x_{\mathrm{fin}} \text{ integral}\}$.
--
--   Geometric and central data. A set $\Phi_K\subseteq \mathrm{GL}_2(\mathbb A_K)$ is given, together with reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}$, $d_{1K}<d_{2K}$, a finite set $T_K\subseteq \mathrm{GL}_2(\mathbb A_K)$, and the hypothesis `hcovK` that the union $\bigcup_{x\in T_K}(\cdot\,x)''\,\mathtt{centreCutSiegelSet}\,K\,c_K\,u_K\,d_{1K}\,d_{2K}$ covers $\mathrm{GL}_2(\mathbb A_K)$ modulo $\mathrm{GL}_2(K)$ on the left and the adelic centre on the right; here the centre-cut Siegel set consists of those $g$ with integral finite part, all local heights at infinite places at least $c_K$, all window parameters bounded by $u_K^2$, and all archimedean determinant norms in $[d_{1K},d_{2K}]$. Further, $\nu_{ZK}$ is a Haar measure on $\mathbb A_K^\times$ (for a given measurable and Borel structure) and $\Omega_K$ is a fundamental domain, in the sense of `IsFundamentalDomain`, for the action of the image of $K^\times$ in $\mathbb A_K^\times$. A finite set $S_K$ of finite places, a character $\xi_K$ of the full group $\top\le\mathbb A_K^\times$ with values in $\mathbb C^\times$ is given, assumed continuous (`hξc`), trivial on the principal ideles (`hξt`) and of absolute value $1$ everywhere (`hξu`); an ideal $N\subseteq \mathcal O_K$ all of whose prime divisors lie in $S_K$ (`hN`); and a family $\mathrm{tys}_K$ of archimedean $K$-types, giving the cut submodule $\mathtt{archCutSubmodule}\,K\,\mathrm{tys}_K=\bigsqcap_w\bigsqcup_i \mathtt{archTypeSubmoduleAt}$.
--
--   The character $\alpha_m : \mathbb A_K^\times \to \mathbb R^\times$ is the module (distributive Haar) character of $\mathbb A_K$, viewed in $\mathbb R^\times$, and `hαm` asserts its positivity; for $s\in\mathbb C$ the twisted characters are $\eta_1(\mu,s)=\mu\cdot\alpha_m^{\,s+1/2}$ and $\eta_2(\nu,s)=\nu\cdot\alpha_m^{-(s+1/2)}$.
--
--   Cuspidal orthonormal basis data. Types $\iota$, a family $b : \iota \to (\mathrm{GL}_2(\mathbb A_K)\to\mathbb C)$ and a labelling $\mathrm{cls} : \iota \to \mathtt{HeckeEigensystem}\,K\,\mathbb C$ are given, subject to four groups of hypotheses: `hb`, that each $\mathrm{cls}\,i$ is a cusp class for $(\mathrm{pins},\xi_K,N,S_K)$ (level $N$, vanishing eigenvalues $a_v=b_v=0$ at $v\in S_K$, and non-vanishing isotypic submodule) and $b\,i$ lies in the isotypic cuspidal submodule of $\mathrm{cls}\,i$ intersected with the archimedean cut submodule; `hbn` and `hbo`, that the $b\,i$ are orthonormal for the inner product $\int_{\Phi_0} b\,i\cdot\overline{b\,j}$; `hbs`, that for every cusp class $\pi$ the fibre $\{i : \mathrm{cls}\,i=\pi\}$ is finite and $b$ spans, over $\mathbb C$, the isotypic submodule of $\pi$ intersected with the archimedean cut submodule; and `hbc`, completeness: any $\varphi$ which is a smooth cuspidal automorphic function for $(\mathrm{pins},\xi_K)$, continuous, right invariant under $U(N)$, of the prescribed archimedean types, and orthogonal to every $b\,i$ over $\Phi_0$, vanishes almost everywhere on $\Phi_0$.
--
--   Continuous-spectrum (Eisenstein) data. A countable type $\iota_E$ with families $\mu,\nu : \iota_E \to \mathrm{Hom}(\mathbb A_K^\times,\mathbb C^\times)$ is given, with the hypotheses (unitarity, triviality on $K^\times$, continuity) for both families, the product relation $\mu_e\,\nu_e=\xi_K$, and separation: distinct $e\neq e'$ are distinguished by some norm-one idele. For each $e$ an integer $n_E(e)$ and sections $\varphi_{e,j}(s)$, $j\in\mathrm{Fin}(n_E(e))$, are given, subject to the hypothesis group: each $\varphi_{e,j}(s)$ is an induced section for $(\eta_1(\mu_e,s),\eta_2(\nu_e,s))$, is archimedean $K$-finite, is smooth for the finite-adelic subgroup, depends jointly continuously on $(s,g)$, is holomorphic in $s$ for each $g$, satisfies a uniform archimedean $K$-finiteness condition (a fixed finite-dimensional space $W$ at each infinite place containing all right translates), is flat in the sense $\varphi_{e,j}(s)(k)=\varphi_{e,j}(0)(k)$ on the maximal compact, is right invariant under $\mathtt{principalLevel}(N)\sqcap$ the finite-adelic subgroup, lies in the archimedean cut submodule, is orthonormal in $j$ for `maximalCompactHaar` on $\mathtt{adelicMaximalCompact}\,K$, and spans: every induced section on the unitary axis $s=it$ for the pair $(\mu_e,\nu_e)$ satisfying the same continuity, $K$-finiteness, level and type conditions lies in the span of the $\varphi_{e,j}(it)$ (`_hφEspan`). The hypothesis `_hpairs` asserts exhaustiveness of the family: for any pair $(\mu',\nu')$ of continuous unitary idele class characters with $\mu'\nu'=\xi_K$, any $t\in\mathbb R$ and any non-zero induced section on the axis with the stated properties, there is $e$ with $\mu_e=\mu'$ and $\nu_e=\nu'$ on the norm-one ideles.
--
--   Continuations. Sets $O_{e,j}\subseteq\mathbb C$ and families $E_{e,j},N_{e,j}$ are given with the hypothesis `_hEE` (nine clauses): $O_{e,j}$ is open and preconnected and contains both the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$; for each $g$ the functions $s\mapsto E_{e,j}(s)(g)$ and $s\mapsto N_{e,j}(s)(g)$ are analytic on a neighbourhood of $O_{e,j}$; both are continuous on $O_{e,j}\times\mathrm{GL}_2(\mathbb A_K)$; and on $\{\mathrm{Re}\,s>1/2\}$ they are given by the Eisenstein sum $E_{e,j}(s)(g)=\varphi_{e,j}(s)(g)+\sum'_{\xi\in K}\varphi_{e,j}(s)(w\,u(\xi)\,g)$, with $w=\mathtt{adelicWeyl}$ and $u$ the upper unipotent embedding, and by the intertwining integral $N_{e,j}(s)(g)=\int_{\mathbb A_K}\varphi_{e,j}(s)(w^{-1}u(x)g)\,dx$ for `adelicAddHaar`.
--
--   Paley–Wiener datum. A finite type $\iota_P$ with families $\mu_P,\nu_P$ of characters is given, with unitarity, triviality on $K^\times$, continuity of both, the relation $\mu_P(e)(z)\,\nu_P(e)(z)=\xi_K(z)$ for $z$ in $Z=\top$, a map $r_P:\iota_P\to\iota_P$ swapping the two families, and separation by norm-one ideles. Sections $\psi_i(s)$ are given with: the induced-section property for $(\eta_1(\mu_P(i),s),\eta_2(\nu_P(i),s))$, joint continuity, holomorphy in $s$, archimedean $K$-finiteness, smoothness for the finite-adelic subgroup, uniform archimedean $K$-finiteness, right invariance under $\mathtt{principalLevel}(N)\sqcap$ the finite-adelic subgroup, membership in the archimedean cut submodule, and the rapid-decay hypothesis `_hψdec`: for every $i$, $n\in\mathbb N$, $\sigma_0\in\mathbb R$ and compact $C$ there is an integrable bounded majorant $m$ with $(1+|t|)^n\,\|\psi_i(\sigma'+it)(g)\|\le m(t)$ for all $|\sigma'|\le\sigma_0$, $t\in\mathbb R$ and $g\in C$. A function $\psi$ is given which is a slab profile for $(Z=\top,\xi_K)$, that is, measurable, invariant under left translation by unipotents $u(x)$ and by global Borel points, transforming by $\xi_K$ under the centre, bounded on each determinant-norm slab $[d_1,d_2]$ with $d_1>0$, and supported in a band $[a,b]$, $a>0$, of adelic heights; and `_hψrep` asserts that for every $\sigma'\in\mathbb R$ and every $g$, $\psi(g)=\sum_i (4\pi)^{-1}\int_{\mathbb R}\psi_i(\sigma'+it)(g)\,dt$. Finally $\mathrm{em}:\iota_P\to\iota_E$ and $\tau:\iota_P\to\mathbb R$ are given with `_hem`: $\mu_P(i)=\mu_{\mathrm{em}(i)}\cdot\|\cdot\|^{i\tau_i}$ and $\nu_P(i)=\nu_{\mathrm{em}(i)}\cdot\|\cdot\|^{-i\tau_i}$, where $\|\cdot\|^{i t}$ is [`NumberField.TateGlobal.normPowChar K t`](def/NumberField_NormPowChar.html#L22).
--
--   Conclusion. Write $c_{ij}(t)=\int_{\mathtt{adelicMaximalCompact}\,K}\psi_i(it)(k)\,\overline{\varphi_{\mathrm{em}(i),j}(i(t+\tau_i))(k)}\,dk$ for `maximalCompactHaar`, and
--   $$P(g)=\sum_{i\in\iota_P}\int_{\mathbb R}\sum_{j\in \mathrm{Fin}(n_E(\mathrm{em}(i)))}c_{ij}(t)\,E_{\mathrm{em}(i),j}\bigl(i(t+\tau_i)\bigr)(g)\,dt .$$
--   Then for every real $R$ and every $x\in\Phi_0$,
--   $$P(x)-\bigl(\Lambda^{e^R}P\bigr)(x)=\mathbf 1_{\{g\,:\,e^R<H(g)\}}(x)\cdot \sum_{i\in\iota_P}\int_{\mathbb R}\sum_{j}c_{ij}(t)\Bigl(\varphi_{\mathrm{em}(i),j}\bigl(i(t+\tau_i)\bigr)(x)+v^{-1}\,N_{\mathrm{em}(i),j}\bigl(i(t+\tau_i)\bigr)(x)\Bigr)\,dt,$$
--   where $H=\mathtt{NumberField.AdelicHeight.adelicHeight}\,K$, $v=\bigl(\mathtt{adelicAddHaar}\,(\mathcal O_K)\,K\,(\mathtt{adelicBox}\,K)\bigr).\mathtt{toReal}$ is the volume of the adelic box, and $\Lambda^{T}F=F-\mathbf 1_{\{H>T\}}\cdot F_{\mathrm{const}}$ is the truncation operator [`AutomorphicForm.lambdaT`](def/AutomorphicForm_TruncationOperator.html#L48) at $T=e^R$, formed with the unipotent embedding $u$ and with the constant term taken for the measure $\mathrm{pins}.\nu$, namely `adelicAddHaar` conditioned on the adelic box. Equivalently, the left-hand side is the indicator of the high set times the constant term of $P$.
--
--   This identifies the part of an Eisenstein wave packet removed by Arthur's truncation operator at height $e^R$: it is the high-set cut-off of the explicit constant-term packet, the constant term of a continued Eisenstein series on the unitary axis being $\varphi(it)+v^{-1}N(it)$ with $v$ the volume of the adelic box. It feeds the square-integrability statement [`AutomorphicForm.memLp_two_restrict_canonicalTruncationDomain_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener`](thm.html#AutomorphicForm.memLp_two_restrict_canonicalTruncationDomain_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener) for such packets on the canonical truncation domain, a step in the spectral decomposition underlying the adelic theory of automorphic forms on $\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_sum_integral_sum_inner_mul_axis_continuation_sub_lambdaT_eq_indicator_highSet_sum_integral_sum_inner_mul_add_inv_vol_mul_weylIntertwining_of_matched_paleyWiener.lean

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

theorem AutomorphicForm.sum_integral_sum_inner_mul_axis_continuation_sub_lambdaT_eq_indicator_highSet_sum_integral_sum_inner_mul_add_inv_vol_mul_weylIntertwining_of_matched_paleyWiener
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
        (fun g : AdelicGL2 (𝓞 K) K =>
            ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)), (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                ∂(maximalCompactHaar K)) * EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) x -
        @AutomorphicForm.lambdaT _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).nS _ _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν
          (fun n => AutomorphicForm.unipotentGL2 n) (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (fun g : AdelicGL2 (𝓞 K) K =>
            ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)), (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                ∂(maximalCompactHaar K)) * EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) x =
          (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)).indicator
            (fun g : AdelicGL2 (𝓞 K) K => ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
              (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                  ∂(maximalCompactHaar K)) *
                (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g +
                  ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g))
            x := by sorry
