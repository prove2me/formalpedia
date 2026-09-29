-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_axis_continuation_mul_conj_cuspBasis_eq_zero_of_mem
-- name    : AutomorphicForm.setIntegral_axis_continuation_mul_conj_cuspBasis_eq_zero_of_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/a8cca5b6-7f59-511e-a9a0-651611be5c5c
-- title:
--   Continued Eisenstein series pair to zero with the cuspidal basis
-- statement:
--   Fix a number field $K$ and reals $\alpha,\beta$ with $0<\alpha$ and $\alpha<\beta$; the integration region throughout is [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32), the third component of the canonically chosen truncation datum attached to the window $(\alpha,\beta)$ (empty if no such datum exists), and the measure is the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` on $\mathrm{GL}_2$ of the adeles, for the Borel $\sigma$-algebra. A further set $\Phi_K$ of adelic matrices is among the arguments but occurs neither in the other hypotheses nor in the conclusion.
--
--   *Siegel covering data.* Reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}<d_{2K}$ and a finite set $T_K\subseteq \mathrm{GL}_2(\mathbb{A}_K)$ are given such that the union $\bigcup_{x\in T_K}(\,\cdot\, x)\bigl[\,\mathrm{centreCutSiegelSet}\;K\;c_K\,u_K\,d_{1K}\,d_{2K}\bigr]$ of right translates satisfies `CoversModCentre K`, i.e. every $g\in\mathrm{GL}_2(\mathbb{A}_K)$ admits $\gamma\in\mathrm{GL}_2(K)$ and an idele unit $z$ with $\gamma g\,\mathrm{diag}(z,z)$ in that union. Here the centre-cut Siegel set consists of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at every infinite place $w$ has $\mathrm{localHeight}=|\det|/\mathrm{rowNormSq}\ge c_K$ and $\mathrm{xWindowSq}\le u_K^2$, and with $\mathrm{archDetNorm}\,w\,g\in[d_{1K},d_{2K}]$ for every $w$.
--
--   *Idele-class data.* The group of idele units carries a measurable structure which is Borel, $\nu_{ZK}$ is a Haar measure on it, and $\Omega_K$ is a fundamental domain for the image of $K^\times$ under `Units.map (algebraMap K (AdeleRing (𝓞 K) K))` with respect to $\nu_{ZK}$. A finite set $S_K$ of finite places, a homomorphism $\xi_K$ from the full subgroup of idele units to $\mathbb{C}^\times$ which is continuous (`hξc`), trivial on the image of $K^\times$ (`hξt`) and of absolute value $1$ everywhere (`hξu`), an ideal $N$ of $\mathcal{O}_K$ all of whose divisor places lie in $S_K$ (`hN`), and an archimedean type family $\mathrm{tys}_K$ (at each infinite place $w$ a finite list of representations of the row-isometry subgroup of $K_w$, cutting out `archCutSubmodule K tysK`) are given. Writing $\alpha_m$ for the idelic module character, the composite of `distribHaarChar (AdeleRing (𝓞 K) K)` with $\mathbb{R}_{\ge0}\to\mathbb{R}$ taken into $\mathbb{R}^\times$, the hypothesis $h_{\alpha m}$ asserts $\alpha_m(x)>0$ for all $x$.
--
--   *The carrier pins.* All automorphic notions below are taken for `productionPinsOf` with domain the canonical truncation domain, level subgroups $M\mapsto$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, Hecke generators $v\mapsto$ `heckeGen (𝓞 K) K v`, central subgroup $\top$, the Borel $\sigma$-algebras and Haar measures on $\mathrm{GL}_2(\mathbb{A}_K)$ and on $\mathbb{A}_K$, the latter conditioned on the box `adelicBox K`.
--
--   *The cuspidal basis.* An index type $\iota$, functions $b:\iota\to(\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ and a class map $\mathrm{cls}:\iota\to$ `HeckeEigensystem K ℂ` are given, subject to: (`hb`) each $\mathrm{cls}\,i$ lies in `cuspClasses K … ξK N SK` (level $N$, vanishing eigenvalues $a_v=b_v=0$ at the places of $S_K$, non-zero isotypic cuspidal submodule) and $b_i$ lies in the intersection of the isotypic cuspidal submodule of $\mathrm{cls}\,i$ with the type-cut submodule; (`hbn`) $\int b_i\overline{b_i}=1$ over the truncation domain; (`hbo`) $\int b_i\overline{b_j}=0$ for $i\ne j$; (`hbs`) for every class $\pi$ in `cuspClasses`, the fibre $\{i\mid \mathrm{cls}\,i=\pi\}$ is finite and the $\mathbb{C}$-span of the corresponding $b_i$ is exactly the isotypic cuspidal submodule of $\pi$ intersected with the type-cut submodule; and (`hbc`) any $\varphi$ which is a smooth cuspidal automorphic function for these pins and $\xi_K$, continuous, invariant under right translation by the level subgroup at $N$, in the type-cut submodule, and orthogonal on the truncation domain to every $b_i$, vanishes almost everywhere for the Haar measure restricted to the truncation domain.
--
--   *The Eisenstein data.* A countable type $\iota_E$ and families of idele characters $\mu,\nu:\iota_E\to(\mathbb{A}_K^\times\to\mathbb{C}^\times)$ are given with: each $\mu_e,\nu_e$ unitary and trivial on $K^\times$ (`_hμ`, `_hν`, `_hμic`, `_hνic`), continuous (`_hμc`, `_hνc`), satisfying $\mu_e\nu_e=\xi_K$ (`_hμν`), and pairwise distinct on the norm-one ideles (`_hdist`). Integers $n_E(e)$ and sections $\varphi_E(e,j,s,\cdot)$ for $j\in\mathrm{Fin}(n_E\,e)$, $s\in\mathbb{C}$ are given, subject to the following hypotheses, which are named but whose content is summarised here: `_hφE` (each $\varphi_E(e,j,s)$ is an induced section for the characters $\eta_1=\mu_e\cdot\alpha_m^{\,s+1/2}$ and $\eta_2=\nu_e\cdot\alpha_m^{-(s+1/2)}$, i.e. transforms by $\eta_1(b_{11})\eta_2(b_{22})$ under left translation by the adelic Borel subgroup), `_hφEK` (archimedean $K$-finiteness at every infinite place), `_hφEf` (smoothness as a vector for the finite adelic subgroup), `_hφEjc` (joint continuity in $(s,g)$), `_hφEhol` (holomorphy in $s$ for each $g$), `_hφEKu` (for each $e,j,w$ a single finite-dimensional space of functions on the row-isometry subgroup at $w$ containing all the restrictions $k\mapsto\varphi_E(e,j,s)(gk)$), `_hφEflat` ($\varphi_E(e,j,s)$ agrees with $\varphi_E(e,j,0)$ on the adelic maximal compact), `_hφElev` (right invariance under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`), `_hφEty` (membership in the type-cut submodule), `_hφEon` (orthonormality of the $\varphi_E(e,j,0)$ over the maximal compact for `maximalCompactHaar K`), `_hφEspan` (for each $e$ and each real $t$, every continuous, archimedean $K$-finite, level-invariant, type-cut induced section for the characters at $s=it$ lies in the span of the $\varphi_E(e,j,it)$), and `_hpairs` (for every pair $\mu',\nu'$ of continuous unitary characters trivial on $K^\times$ with $\mu'\nu'=\xi_K$, every real $t$ and every non-zero section at $s=it$ satisfying the same conditions, some $e$ has $\mu_e=\mu'$ and $\nu_e=\nu'$ on the norm-one ideles).
--
--   *The continuations.* Sets $O_E(e,j)\subseteq\mathbb{C}$ and families $E_E(e,j,s,\cdot)$, $N_E(e,j,s,\cdot)$ are given, and the hypothesis `_hEE` requires for each $e,j$: $O_E(e,j)$ is open, preconnected, and contains both the imaginary axis $\{\operatorname{Re}s=0\}$ and the half-plane $\{\operatorname{Re}s>1/2\}$; for every $g$ the functions $s\mapsto E_E(e,j,s,g)$ and $s\mapsto N_E(e,j,s,g)$ are analytic on a neighbourhood of $O_E(e,j)$; both $(s,g)\mapsto E_E(e,j,s,g)$ and $(s,g)\mapsto N_E(e,j,s,g)$ are continuous on $O_E(e,j)\times\mathrm{GL}_2(\mathbb{A}_K)$; for $\operatorname{Re}s>1/2$ one has the Eisenstein expansion $E_E(e,j,s,g)=\varphi_E(e,j,s)(g)+\sum_{\xi\in K}\varphi_E(e,j,s)\bigl(w\,u(\xi)\,g\bigr)$ with $w=$ `adelicWeyl` and $u(\xi)=$ `unipotentGL2` of the image of $\xi$; and for $\operatorname{Re}s>1/2$ one has $N_E(e,j,s,g)=$ `weylIntertwiningIntegral` of $\varphi_E(e,j,s)$ at $g$, namely $\int_{\mathbb{A}_K}\varphi_E(e,j,s)(w^{-1}u(x)g)\,dx$ for the adelic additive Haar measure.
--
--   Under all of this, for every $e\in\iota_E$, every $j\in\mathrm{Fin}(n_E\,e)$, every $s\in O_E(e,j)$ and every $i\in\iota$,
--   $$\int_{\mathrm{canonicalTruncationDomain}\,K\,\alpha\,\beta} E_E(e,j,s,g)\,\overline{b_i(g)}\;d\bigl(\mathrm{adelicGLHaar}\,(\mathrm{Fin}\,2)\,\mathcal{O}_K\,K\bigr)(g)=0 .$$
--
--   This is the orthogonality of the continued Eisenstein series to the cuspidal spectrum, stated over the whole continuation domain $O_E(e,j)$ rather than only on the half-plane of absolute convergence, where it follows from the vanishing of constant terms of cusp forms. It is used in the construction of the spectral expansion on the truncation domain, being cited by [`AutomorphicForm.forall_axis_continuation_sub_sum_mul_axis_continuation_eq_zero_of_forall_constantTerm_eq_zero`](thm.html#AutomorphicForm.forall_axis_continuation_sub_sum_mul_axis_continuation_eq_zero_of_forall_constantTerm_eq_zero) and by [`AutomorphicForm.setIntegral_sum_integral_sum_inner_mul_axis_continuation_mul_conj_cuspBasis_eq_zero_of_matched_paleyWiener`](thm.html#AutomorphicForm.setIntegral_sum_integral_sum_inner_mul_axis_continuation_mul_conj_cuspBasis_eq_zero_of_matched_paleyWiener).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_axis_continuation_mul_conj_cuspBasis_eq_zero_of_mem.lean

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

theorem AutomorphicForm.setIntegral_axis_continuation_mul_conj_cuspBasis_eq_zero_of_mem
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
      (e : ιE) (j : Fin (nE e)) (s : ℂ) (_hs : s ∈ OE e j) (i : ι),
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, EE e j s g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by sorry
