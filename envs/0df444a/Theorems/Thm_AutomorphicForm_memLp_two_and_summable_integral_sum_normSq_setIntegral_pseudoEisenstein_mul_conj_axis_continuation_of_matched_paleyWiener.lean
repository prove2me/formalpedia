-- Prove2me | Theorems.Thm_AutomorphicForm_memLp_two_and_summable_integral_sum_normSq_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_of_matched_paleyWiener
-- name    : AutomorphicForm.memLp_two_and_summable_integral_sum_normSq_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_of_matched_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/2bf03e15-8869-5bd7-abb8-c2c4e9b88de8
-- title:
--   Square-summability of the Eisenstein coefficients of a matched Paley–Wiener profile
-- statement:
--   Let $K$ be a number field. Fix reals $\alpha,\beta$ with $0<\alpha<\beta$, and let $D=\mathtt{canonicalTruncationDomain}\,K\,\alpha\,\beta$ be the canonical truncation domain attached to $(\alpha,\beta)$ (the third component of the canonically chosen truncation datum, empty if none exists). A set $\Phi_K$ of elements of $\mathrm{GL}_2$ of the adeles enters as a parameter on which no condition is imposed.
--
--   **Siegel covering data.** Reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}<d_{2K}$ and a finite set $T_K\subseteq \mathrm{GL}_2(\mathbb{A}_K)$ are given, together with the hypothesis `hcovK` that the union $\bigcup_{x\in T_K}(\,\cdot\,x)\bigl[\mathtt{centreCutSiegelSet}\,K\,c_K\,u_K\,d_{1K}\,d_{2K}\bigr]$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo the centre, i.e. for every $g$ there exist $\gamma\in \mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g\,z$ in that union; here the centre-cut Siegel set consists of those $g$ whose finite part is integral, whose local height at each infinite place is $\ge c_K$, whose window quantity $\mathtt{xWindowSq}$ at each infinite place is $\le u_K^2$, and whose archimedean determinant norms all lie in $[d_{1K},d_{2K}]$.
--
--   **Central measure data.** A measurable and Borel structure on the idele units, a Haar measure $\nu_{Z K}$ on them, and a set $\Omega_K$ which by `hΩK` is a fundamental domain for the image of $K^\times$ in the ideles with respect to $\nu_{ZK}$.
--
--   **Character, level and type data.** A finite set $S_K$ of finite places; a homomorphism $\xi_K$ from the full subgroup $\top$ of the idele units to $\mathbb{C}^\times$, continuous (`hξc`), trivial on principal ideles (`hξt`) and of absolute value $1$ everywhere (`hξu`); an ideal $N$ of $\mathcal{O}_K$ such that every place dividing $N$ lies in $S_K$ (`hN`); and an archimedean type family $\mathtt{tysK}$, i.e. for each infinite place $w$ a finite list of representations of the row-isometry subgroup at $w$, cutting out the submodule $\mathtt{archCutSubmodule}\,K\,\mathtt{tysK}=\bigsqcap_w\bigsqcup_i\mathtt{archTypeSubmoduleAt}$.
--
--   Write $\alpha_m$ for the homomorphism from the idele units to $\mathbb{R}^\times$ obtained from the module character $\mathtt{distribHaarChar}$ of $\mathbb{A}_K$ composed with $\mathbb{R}_{\ge 0}\to\mathbb{R}$, and assume `hαm`, that all its values are positive. For an idele class character $\chi$ and $s\in\mathbb{C}$, $\mathtt{etaFst}\,\chi\,\alpha_m\,s=\chi\cdot\alpha_m^{\,s+1/2}$ and $\mathtt{etaSnd}\,\chi\,\alpha_m\,s=\chi\cdot\alpha_m^{-(s+1/2)}$.
--
--   Throughout, the carrier data is $\mathtt{productionPinsOf}$ with domain $D$, level subgroups $M\mapsto \mathtt{principalLevel}\,N'\sqcap\mathtt{finiteAdelicGL2Subgroup}$, Hecke generators $v\mapsto\mathtt{heckeGen}\,v$ and box $\mathtt{adelicBox}\,K$; its measurable structures are the Borel ones, its measure on $\mathrm{GL}_2(\mathbb{A}_K)$ is $\mathtt{adelicGLHaar}$, its central subgroup is all of the idele units, and its measure on $\mathbb{A}_K$ is additive Haar measure conditioned on $\mathtt{adelicBox}\,K$.
--
--   **Cuspidal basis data.** A type $\iota$, functions $b:\iota\to(\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ and $\mathtt{cls}:\iota\to$ Hecke eigensystems over $\mathbb{C}$, subject to: `hb`, each $\mathtt{cls}\,i$ lies in $\mathtt{cuspClasses}$ for the above pins, $\xi_K$, $N$, $S_K$ (level $N$, vanishing $a_v,b_v$ at $v\in S_K$, non-zero isotypic cusp submodule) and $b\,i$ lies in the isotypic cusp submodule of $\mathtt{cls}\,i$ intersected with the archimedean type submodule; `hbn`, $\int_D b\,i\cdot\overline{b\,i}=1$; `hbo`, $\int_D b\,i\cdot\overline{b\,j}=0$ for $i\neq j$, both integrals taken against $\mathtt{adelicGLHaar}$; `hbs`, for every cusp class $\pi$ the fibre $\{i\mid \mathtt{cls}\,i=\pi\}$ is finite and the $\mathbb{C}$-span of $b$ over it is the $\pi$-isotypic cusp submodule intersected with the archimedean type submodule; and `hbc`, completeness: any $\varphi$ which is a smooth cuspidal automorphic function at these pins for $\xi_K$, is continuous, is right invariant under the level subgroup at $N$, lies in the archimedean type submodule and satisfies $\int_D\varphi\cdot\overline{b\,i}=0$ for all $i$, vanishes almost everywhere on $D$ for $\mathtt{adelicGLHaar}$ restricted to $D$.
--
--   **Eisenstein index family.** A countable type $\iota_E$ and characters $\mu,\nu:\iota_E\to(\mathbb{A}_K^\times\to\mathbb{C}^\times)$, with the hypotheses (grouped here) that each $\mu e,\nu e$ is unitary, trivial on $K^\times$ and continuous, that $\mu e\cdot\nu e=\xi_K$, and that distinct indices are separated by some norm-one idele. For each $e$ a natural number $n_E e$ and sections $\varphi_E\,e\,j\,s$ are given, subject to the following group of hypotheses, summarised here: each $\varphi_E\,e\,j\,s$ is an induced section for the pair $(\mathtt{etaFst}(\mu e)\,s,\mathtt{etaSnd}(\nu e)\,s)$, is archimedean $K$-finite and $K_f$-smooth, is jointly continuous in $(s,g)$ and holomorphic in $s$ for each $g$, has its right translates under the row-isometry subgroup at each infinite place contained in a fixed finite-dimensional space independent of $s$, is flat (its restriction to the adelic maximal compact is independent of $s$), is right invariant under $\mathtt{principalLevel}\,N\sqcap\mathtt{finiteAdelicGL2Subgroup}$, lies in the archimedean type submodule, and for each $e$ the sections $\varphi_E\,e\,j\,0$ are orthonormal on the adelic maximal compact for $\mathtt{maximalCompactHaar}$. Two further spanning hypotheses are imposed: `_hφEspan`, for every $e$, every $t\in\mathbb{R}$ and every induced section $\varphi_0$ for $(\mathtt{etaFst}(\mu e)(it),\mathtt{etaSnd}(\nu e)(it))$ which is continuous, archimedean $K$-finite, level invariant and of the prescribed archimedean type, $\varphi_0$ lies in the span of the $\varphi_E\,e\,j\,(it)$; and `_hpairs`, every pair $(\mu',\nu')$ of continuous unitary characters trivial on $K^\times$ with $\mu'\nu'=\xi_K$ admitting a non-zero such section on the axis agrees with some $(\mu e,\nu e)$ on the norm-one ideles.
--
--   **Axis continuations.** Sets $O_E\,e\,j\subseteq\mathbb{C}$ and families $E_E,N_E$ are given, with `_hEE` asserting: $O_E\,e\,j$ is open and preconnected and contains both the imaginary axis $\{\operatorname{Re}s=0\}$ and the half-plane $\{\operatorname{Re}s>1/2\}$; for each $g$ the functions $s\mapsto E_E\,e\,j\,s\,g$ and $s\mapsto N_E\,e\,j\,s\,g$ are analytic on a neighbourhood of $O_E\,e\,j$; both are continuous on $O_E\,e\,j\times\mathrm{univ}$ as functions of $(s,g)$; for $\operatorname{Re}s>1/2$, $E_E\,e\,j\,s\,g=\varphi_E\,e\,j\,s\,g+\sum_{\xi\in K}'\varphi_E\,e\,j\,s\,(w\,u(\xi)\,g)$ with $w$ the adelic Weyl element and $u(\xi)$ the unipotent matrix; and for $\operatorname{Re}s>1/2$, $N_E\,e\,j\,s\,g$ is the Weyl intertwining integral of $\varphi_E\,e\,j\,s$ at $g$ against additive adelic Haar measure.
--
--   **Paley–Wiener datum.** A finite type $\iota_P$ and characters $\mu_P,\nu_P:\iota_P\to(\mathbb{A}_K^\times\to\mathbb{C}^\times)$, with hypotheses (grouped) that each is unitary, trivial on $K^\times$ and continuous, that $\mu_P e\cdot\nu_P e=\xi_K$ on the central subgroup, that a map $r_P:\iota_P\to\iota_P$ interchanges $\mu_P$ and $\nu_P$, and that distinct indices are separated on the norm-one ideles. Sections $\psi_f\,e\,s$ are induced sections for $(\mathtt{etaFst}(\mu_P e)\,s,\mathtt{etaSnd}(\nu_P e)\,s)$, jointly continuous in $(s,g)$ and entire in $s$ for each $g$, and `_hψdec` requires rapid decay on vertical strips uniformly on compacta: for all $e$, $n\in\mathbb{N}$, $\sigma_0\in\mathbb{R}$ and compact $C$ there is an integrable, bounded-above $m:\mathbb{R}\to\mathbb{R}$ with $(1+|t|)^n\|\psi_f\,e\,(\sigma'+it)\,g\|\le m(t)$ for all $|\sigma'|\le\sigma_0$, all $t$ and all $g\in C$. A function $\psi$ on $\mathrm{GL}_2(\mathbb{A}_K)$ satisfies `_hψ`, that it is a slab profile for the central subgroup $\top$ and $\xi_K$: measurable, invariant under left multiplication by unipotents and by global Borel elements, transforming by $\xi_K$ under the centre, bounded on every slab $\{d_1\le\|\det g\|\le d_2\}$ with $d_1>0$, and with adelic height confined to a band $[a,b]$, $a>0$, on its support. Further, `_hψrep`: for every $\sigma'\in\mathbb{R}$ and every $g$, $\psi(g)=\sum_{e\in\iota_P}(4\pi)^{-1}\int_{\mathbb{R}}\psi_f\,e\,(\sigma'+it)\,g\,dt$. Finally maps $\mathtt{em}:\iota_P\to\iota_E$ and $\tau:\iota_P\to\mathbb{R}$ satisfy `_hem`: $\mu_P i=\mu(\mathtt{em}\,i)\cdot\mathtt{normPowChar}(\tau i)$ and $\nu_P i=\nu(\mathtt{em}\,i)\cdot\mathtt{normPowChar}(\tau i)^{-1}$.
--
--   **Conclusion.** Put
--   $$\Theta(e,j,t)=\int_{D}\bigl(\mathtt{pseudoEisenstein}\,K\,\psi\bigr)(g)\,\overline{E_E\,e\,j\,(it)\,(g)}\;d\bigl(\mathtt{adelicGLHaar}\bigr),$$
--   where $\mathtt{pseudoEisenstein}\,K\,\psi\,(g)=\psi(g)+\sum_{\beta\in K}'\psi(w\,u(\beta)\,g)$. Then both of the following hold.
--
--   First, for every $e\in\iota_E$ and every $j\in\mathrm{Fin}(n_E e)$, the function $t\mapsto\Theta(e,j,t)$ belongs to $L^2$ of $\mathbb{R}$ for Lebesgue measure.
--
--   Second, the family
--   $$e\;\longmapsto\;\int_{\mathbb{R}}\sum_{j\in\mathrm{Fin}(n_E e)}\bigl\|\Theta(e,j,t)\bigr\|^{2}\,dt$$
--   is summable over $\iota_E$.
--
--   This is the square-summability statement for the continuous part of the spectral expansion of a pseudo-Eisenstein series on $\mathrm{GL}_2$ over a number field: the coefficients of $\theta_\psi$ against the Eisenstein continuations $E_{e,j}$ along the unitary axis form an element of $L^2(\mathbb{R})\otimes\ell^2$ over the Eisenstein index family. It is used by [`AutomorphicForm.exists_matched_paleyWiener_pair_eq_and_threeWay_of_matched_paleyWiener_of_matched_paleyWiener`](thm.html#AutomorphicForm.exists_matched_paleyWiener_pair_eq_and_threeWay_of_matched_paleyWiener_of_matched_paleyWiener), where it is invoked for each of two matched Paley–Wiener data in the three-way comparison of cuspidal, residual and continuous contributions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_memLp_two_and_summable_integral_sum_normSq_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_of_matched_paleyWiener.lean

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

theorem AutomorphicForm.memLp_two_and_summable_integral_sum_normSq_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_of_matched_paleyWiener
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
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹),
    (∀ (e : ιE) (j : Fin (nE e)), MemLp (fun t : ℝ => (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) 2) ∧
    Summable (fun e : ιE => ∫ t : ℝ, ∑ j : Fin (nE e), ‖(∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))‖ ^ (2 : ℕ)) := by sorry
