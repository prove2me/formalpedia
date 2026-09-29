-- Prove2me | Theorems.Thm_AutomorphicForm_continuous_and_continuous_pseudoEisenstein_of_paleyWiener_slabProfile
-- name    : AutomorphicForm.continuous_and_continuous_pseudoEisenstein_of_paleyWiener_slabProfile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/6d9f9ef2-102c-5c7a-a35c-1b659b45d51a
-- title:
--   Continuity of a Paley–Wiener slab profile and its pseudo-Eisenstein series
-- statement:
--   Throughout, $K$ is a number field, and $\alpha,\beta$ are reals with $0<\alpha$ and $\alpha<\beta$; the set $\Phi_K\subseteq \mathrm{GL}_2(\mathbb{A}_K)$ enters as a parameter on which no condition is imposed and which does not occur in the conclusion.
--
--   **Siegel covering data.** Reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}$, $d_{1K}<d_{2K}$, and a finite set $T_K$ of adelic matrices are given, together with `hcovK`: the finite union $\bigcup_{x\in T_K}(\cdot\,x)''\,\mathrm{centreCutSiegelSet}\,K\,c_K\,u_K\,d_{1K}\,d_{2K}$ of right translates satisfies `CoversModCentre`, i.e. every $g\in \mathrm{GL}_2(\mathbb{A}_K)$ can be written so that $\gamma g\cdot z$ lies in that union for some $\gamma\in\mathrm{GL}_2(K)$ (embedded by `globalPoints`) and some central scalar $z$ coming from an idele. Here the centre-cut Siegel set consists of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean components satisfy $c_K\le \mathrm{localHeight}$ and $\mathrm{xWindowSq}\le u_K^2$ at every infinite place, and for which $\mathrm{archDetNorm}\,w\,g\in[d_{1K},d_{2K}]$ at every infinite place $w$.
--
--   **Idele-class data.** The idele group $\mathbb{A}_K^\times$ carries a measurable structure which is the Borel structure of its topology, $\nu_{Z,K}$ is a Haar measure on it, and $\Omega_K$ is a fundamental domain, with respect to $\nu_{Z,K}$, for the range of $K^\times\to\mathbb{A}_K^\times$. A finite set $S_K$ of finite places is given, and $\xi_K$ is a homomorphism from the full subgroup $\top\le\mathbb{A}_K^\times$ to $\mathbb{C}^\times$ which is continuous (`hξc`), trivial on the image of $K^\times$ (`hξt`) and unitary, $\lvert\xi_K(z)\rvert=1$ for all $z$ (`hξu`). An ideal $N\subseteq\mathcal{O}_K$ is given with `hN`: every finite place dividing $N$ belongs to $S_K$. Finally $\mathrm{tys}_K$ is an `ArchTypeFamily` for $K$, that is, a cardinality function on infinite places together with, for each infinite place $w$, that many representations of the row-isometry group of $K_w$.
--
--   **The module character.** $\alpha_m$ denotes the homomorphism $\mathbb{A}_K^\times\to\mathbb{R}^\times$ obtained from the module character `distribHaarChar (AdeleRing (𝓞 K) K)` with values in $\mathbb{R}_{\ge0}$, pushed into $\mathbb{R}$ and viewed as a homomorphism to units; the adele ring is given its Borel structure. The remaining hypotheses are taken under the assumption $\alpha_m(x)>0$ for all $x$ (`hαm`).
--
--   **The pins.** All automorphic notions below are taken with respect to the carrier `productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: the Borel structure and Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` on $\mathrm{GL}_2(\mathbb{A}_K)$, the canonical truncation domain of the slab $(\alpha,\beta)$ as integration domain, central subgroup $Z=\top$, level subgroups $U(M)=\mathrm{principalLevel}(M)\cap\ker(\text{archimedean projection})$, Hecke generators $\mathrm{heckeGen}\,v$, and, on the adele ring, its Borel structure with the additive Haar measure conditioned on the box `adelicBox K`.
--
--   **Cuspidal basis data.** An index type $\iota$, functions $b:\iota\to(\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ and $\mathrm{cls}:\iota\to\mathrm{HeckeEigensystem}\,K\,\mathbb{C}$ are given, subject to: `hb`, each $\mathrm{cls}\,i$ lies in `cuspClasses K pins ξK N SK` and $b\,i$ lies in the intersection of the isotypic cuspidal submodule of $\mathrm{cls}\,i$ with the type-cut submodule $\mathrm{archCutSubmodule}\,K\,\mathrm{tys}_K$ (the infimum over infinite places $w$ of the supremum of the type submodules attached to the representations $\mathrm{tys}_K.\mathrm{rep}\,w\,i$); `hbn`, each $b\,i$ has $\int_{D} b\,i\cdot\overline{b\,i}=1$ over the canonical truncation domain $D$ against the adelic Haar measure; `hbo`, the corresponding integrals of $b\,i\cdot\overline{b\,j}$ vanish for $i\ne j$; `hbs`, for every cusp class $\pi$ the fibre $\{i\mid \mathrm{cls}\,i=\pi\}$ is finite and the $\mathbb{C}$-span of $b$ on it is the intersection of the isotypic cuspidal submodule of $\pi$ with the type-cut submodule; and `hbc`, a completeness clause: any $\varphi$ which satisfies `IsSmoothCuspAutomorphicFnAt K pins ξK` (the predicate `IsAutomorphicFnAt` for these pins and $\xi_K$, together with vanishing of the unipotent constant-term integral against the conditioned adelic measure, and smoothness under `finiteAdelicGL2Subgroup`), is continuous, is right invariant under $U(N)$, lies in the type-cut submodule and is orthogonal to every $b\,i$ over $D$, vanishes almost everywhere for the adelic Haar measure restricted to $D$.
--
--   **Continuous-spectrum data.** A countable type $\iota_E$ and families $\mu,\nu:\iota_E\to(\mathbb{A}_K^\times\to\mathbb{C}^\times)$ are given with the hypotheses that each $\mu_e,\nu_e$ is unitary and trivial on $K^\times$, that each is continuous, that $\mu_e\nu_e=\xi_K$, and that distinct indices are separated on the norm-one ideles (the kernel of the module character). For each $e$ a number $n_E(e)$ and a family $\varphi_{E}(e,j,s,\cdot)$, $j<n_E(e)$, of functions on $\mathrm{GL}_2(\mathbb{A}_K)$ are given, subject to hypotheses (summarised here, and each imposed for all $e$, $j$, $s$) that each $\varphi_E(e,j,s,\cdot)$ is an induced section for the pair $\mathrm{etaFst}(\mu_e,\alpha_m,s)=\mu_e\cdot\alpha_m^{s+1/2}$, $\mathrm{etaSnd}(\nu_e,\alpha_m,s)=\nu_e\cdot\alpha_m^{-(s+1/2)}$ — that is, $\varphi(bg)$ equals the product of these characters evaluated on the two diagonal entries of $b$ times $\varphi(g)$, for $b$ in the adelic Borel subgroup — is archimedean $K$-finite, is $K_f$-smooth, is jointly continuous in $(s,g)$, is entire in $s$ for each $g$, satisfies a uniform archimedean $K$-finiteness clause (a single finite-dimensional space $W$ of functions on the row-isometry subgroup at each infinite place containing all right translates), is flat, i.e. agrees at $s$ and at $0$ on the maximal compact subgroup, is right invariant under $\mathrm{principalLevel}(N)\cap\ker(\text{archimedean projection})$, lies in the type-cut submodule, is orthonormal on the maximal compact group at $s=0$ against `maximalCompactHaar K`, and spans: on the unitary axis $s=it$ every continuous archimedean $K$-finite induced section for $(\mu_e,\nu_e)$ of level $N$ and of the given types lies in the span of the $\varphi_E(e,j,it,\cdot)$. The hypothesis `_hpairs` requires moreover that any pair $(\mu',\nu')$ of continuous unitary idele-class characters with $\mu'\nu'=\xi_K$ carrying a nonzero continuous archimedean $K$-finite induced section of level $N$ and of the given types on the unitary axis agrees with some $(\mu_e,\nu_e)$ on the norm-one ideles.
--
--   **Axis continuations.** Sets $O_E(e,j)\subseteq\mathbb{C}$ and families $E_E(e,j,\cdot,\cdot)$, $N_E(e,j,\cdot,\cdot)$ are given with `_hEE`: each $O_E(e,j)$ is open and preconnected and contains both the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$; for each $g$ both $s\mapsto E_E(e,j,s,g)$ and $s\mapsto N_E(e,j,s,g)$ are analytic on a neighbourhood of $O_E(e,j)$; both are continuous on $O_E(e,j)\times\mathrm{GL}_2(\mathbb{A}_K)$ as functions of $(s,g)$; and for $\mathrm{Re}\,s>1/2$ one has $E_E(e,j,s,g)=\varphi_E(e,j,s,g)+\sum_{\xi\in K}\varphi_E\bigl(e,j,s,\,w\,u(\xi)\,g\bigr)$ with $w=\mathrm{adelicWeyl}$ and $u(\xi)$ the unipotent matrix with upper-right entry $\xi$, and $N_E(e,j,s,g)$ equals the Weyl intertwining integral $\int_{\mathbb{A}_K}\varphi_E(e,j,s,\,w^{-1}u(x)g)\,dx$ against the additive adelic Haar measure.
--
--   **The Paley–Wiener datum.** A finite type $\iota_P$ and families $\mu_P,\nu_P:\iota_P\to(\mathbb{A}_K^\times\to\mathbb{C}^\times)$ are given, each $\mu_P(e),\nu_P(e)$ unitary, trivial on $K^\times$ and continuous, with $\mu_P(e)(z)\nu_P(e)(z)=\xi_K(z)$ for $z$ in the central subgroup $\top$ of the pins, together with a map $r_P:\iota_P\to\iota_P$ swapping the two characters ($\mu_P(r_Pe)=\nu_P(e)$ and $\nu_P(r_Pe)=\mu_P(e)$) and a separation clause for distinct indices on the norm-one ideles. A family $\psi_f(e,s,\cdot)$ is given with: each $\psi_f(e,s,\cdot)$ an induced section for $\mathrm{etaFst}(\mu_P(e),\alpha_m,s)$, $\mathrm{etaSnd}(\nu_P(e),\alpha_m,s)$; joint continuity in $(s,g)$; entirety in $s$; archimedean $K$-finiteness, $K_f$-smoothness and the uniform archimedean $K$-finiteness clause; right invariance under $\mathrm{principalLevel}(N)\cap\ker(\text{archimedean projection})$ and membership in the type-cut submodule; and the rapid-decay hypothesis `_hψdec`: for every $e$, every $n\in\mathbb{N}$, every $\sigma_0\in\mathbb{R}$ and every compact $C$ there is an integrable, bounded above $m:\mathbb{R}\to\mathbb{R}$ with $(1+\lvert t\rvert)^n\lVert\psi_f(e,\sigma'+it,g)\rVert\le m(t)$ for all $\lvert\sigma'\rvert\le\sigma_0$, all $t$ and all $g\in C$.
--
--   Finally $\psi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ satisfies `IsSlabProfile K ⊤ ξK ψ`, i.e. $\psi$ is measurable, invariant under left multiplication by adelic unipotents, invariant under left multiplication by global elements of the Borel subgroup, transforms by $\xi_K$ under left multiplication by central scalars, is bounded on each determinant-idele-norm slab $[d_1,d_2]$ with $d_1>0$, and is supported where the adelic height lies in some band $[a,b]$ with $a>0$; the wave-packet representation `_hψrep` asserts that for every $\sigma'\in\mathbb{R}$ and every $g$, $\psi(g)=\sum_{e\in\iota_P}(4\pi)^{-1}\int_{\mathbb{R}}\psi_f(e,\sigma'+it,g)\,dt$; and the matching data $e_m:\iota_P\to\iota_E$, $\tau:\iota_P\to\mathbb{R}$ satisfy `_hem`: $\mu_P(i)=\mu(e_m i)\cdot\lVert\cdot\rVert^{i\tau(i)}$ and $\nu_P(i)=\nu(e_m i)\cdot\lVert\cdot\rVert^{-i\tau(i)}$ in terms of [`NumberField.TateGlobal.normPowChar`](def/NumberField_NormPowChar.html#L22). The level and type hypotheses `_hψlev`, `_hψty` repeat for $\psi_f$ the invariance under $\mathrm{principalLevel}(N)\cap\ker(\text{archimedean projection})$ and membership in $\mathrm{archCutSubmodule}\,K\,\mathrm{tys}_K$.
--
--   **Conclusion.** Two assertions hold: first, $\psi$ is continuous on $\mathrm{GL}_2(\mathbb{A}_K)$; second, the pseudo-Eisenstein series [`AutomorphicForm.pseudoEisenstein K ψ`](def/AutomorphicForm_SlabProfile.html#L32), namely $g\mapsto \psi(g)+\sum_{\beta\in K}\psi\bigl(w\,u(\beta)\,g\bigr)$ with $w$ the adelic image of the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $u(\beta)$ the unipotent with upper-right entry $\beta$, is continuous as well.
--
--   The result supplies the regularity input for the continuous part of the spectral decomposition: a slab profile assembled as a one-dimensional wave packet of rapidly decreasing holomorphic induced sections is continuous, and so is the associated pseudo-Eisenstein series, the local finiteness of whose defining sum comes from [`AutomorphicForm.finite_support_pseudoEisenstein_summand`](thm.html#AutomorphicForm.finite_support_pseudoEisenstein_summand) together with the invariance and comparison properties of the adelic height. It is used by [`AutomorphicForm.exists_forall_pseudoEisenstein_sub_residualProj_ae_eq_mul_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener`](thm.html#AutomorphicForm.exists_forall_pseudoEisenstein_sub_residualProj_ae_eq_mul_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener), where continuity is needed before the cuspidal completeness clause and the cuspidality criterion can be applied.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuous_and_continuous_pseudoEisenstein_of_paleyWiener_slabProfile.lean

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

theorem AutomorphicForm.continuous_and_continuous_pseudoEisenstein_of_paleyWiener_slabProfile
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
    Continuous ψ ∧ Continuous (AutomorphicForm.pseudoEisenstein K ψ) := by sorry
