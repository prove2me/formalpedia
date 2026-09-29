-- Prove2me | Theorems.Thm_AutomorphicForm_continuous_setIntegral_mul_conj_axis_continuation_and_exists_norm_le_mul_one_add_abs_pow_of_isAutomorphicFnAt_of_lt_adelicHeight
-- name    : AutomorphicForm.continuous_setIntegral_mul_conj_axis_continuation_and_exists_norm_le_mul_one_add_abs_pow_of_isAutomorphicFnAt_of_lt_adelicHeight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/ab1ce762-5e8e-56b3-8f39-c2ca66e6faa8
-- title:
--   Continuity and polynomial growth of Eisenstein coefficients
-- statement:
--   Throughout, $K$ is a number field, $\mathbb{A}_K$ denotes its adele ring, $\mathrm{GL}_2(\mathbb{A}_K)$ (written `AdelicGL2 (𝓞 K) K`) carries its Borel $\sigma$-algebra and Haar measure `adelicGLHaar`, and $D :=$ [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) is the subset of $\mathrm{GL}_2(\mathbb{A}_K)$ selected as the third component of `canonicalTruncationData K α β`, i.e. of a datum chosen to satisfy `IsTruncationDatum K α β` for the slab determined by two reals $\alpha<\beta$ with $0<\alpha$. All spectral data are taken relative to the carrier pins
--   $$\mathrm{pins} := \mathtt{productionPinsOf}\,K\,D\,(M \mapsto \mathtt{principalLevel}(\mathcal{O}_K,K,M) \sqcap \mathtt{finiteAdelicGL2Subgroup}\,K)\,(v \mapsto \mathtt{heckeGen}(\mathcal{O}_K,K,v))\,(\mathtt{adelicBox}\,K),$$
--   whose measure is the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, whose domain is $D$, whose central subgroup is all of $(\mathbb{A}_K)^\times$, whose level subgroups are the principal level groups at $M$ intersected with the kernel of the archimedean projection, whose Hecke generators are the elements `heckeGen`, and whose adelic measure is additive Haar measure conditioned on the adelic box.
--
--   The data and hypotheses are as follows.
--
--   Slab and covering data: reals $\alpha,\beta$ with $0<\alpha$ and $\alpha<\beta$; a set $\Phi_K \subseteq \mathrm{GL}_2(\mathbb{A}_K)$, which carries no hypothesis and does not occur in the conclusion; reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$ and $0<d_{1K}<d_{2K}$; a finite set $T_K \subseteq \mathrm{GL}_2(\mathbb{A}_K)$; and the hypothesis `hcovK`, stating that the union over $x \in T_K$ of the right translates by $x$ of `centreCutSiegelSet K cK uK d₁K d₂K` covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo the centre in the sense of `CoversModCentre`: for every $g$ there are $\gamma \in \mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g \cdot z$ (image of $\gamma$ under `globalPoints` times $g$ times the central scalar attached to $z$) in that union. Here the centre-cut Siegel set consists of those $g$ whose finite part is integral, whose archimedean components all have local height at least $c_K$ and window $\mathtt{xWindowSq} \le u_K^2$, and whose archimedean determinant norms all lie in $[d_{1K},d_{2K}]$.
--
--   Central measure data: a measurable space and Borel space structure on $(\mathbb{A}_K)^\times$, a Haar measure $\nu_{ZK}$ on $(\mathbb{A}_K)^\times$, and a set $\Omega_K$ which by `hΩK` is a fundamental domain for the range of $K^\times \to (\mathbb{A}_K)^\times$ with respect to $\nu_{ZK}$.
--
--   Character, level and type data: a finite set $S_K$ of finite places of $K$; a homomorphism $\xi_K$ from the full subgroup of $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$, with `hξc` asserting continuity of $z \mapsto \xi_K(z)$, `hξt` asserting $\xi_K(z)=1$ for $z$ in the image of $K^\times$, and `hξu` asserting $\lVert \xi_K(z)\rVert = 1$ for all $z$; an ideal $N \subseteq \mathcal{O}_K$ with `hN` asserting that every finite place whose prime divides $N$ lies in $S_K$; and an archimedean type family $\mathrm{tys}_K$, giving at each infinite place $w$ a finite list of representations of the row-isometry subgroup, whence the submodule `archCutSubmodule K tysK`, the infimum over infinite places of the sums of the corresponding type submodules.
--
--   The module character: $\alpha_m$ is introduced as the homomorphism $(\mathbb{A}_K)^\times \to \mathbb{R}^\times$ obtained from the distributive Haar character of $\mathbb{A}_K$ composed with $\mathbb{R}_{\ge 0} \to \mathbb{R}$, and the statement is then universally quantified over a proof `hαm` that $\alpha_m(x)>0$ for all $x$; $\alpha_m$ and `hαm` are the arguments of the character families `etaFst`, `etaSnd`, where $\mathtt{etaFst}\,\mu\,\alpha_m\,h\,s = \mu\cdot\alpha_m^{\,s+1/2}$ and $\mathtt{etaSnd}\,\nu\,\alpha_m\,h\,s = \nu\cdot\alpha_m^{-(s+1/2)}$.
--
--   Cuspidal basis data: a type $\iota$, functions $b_i : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ and Hecke eigensystems $\mathrm{cls}(i) \in$ `HeckeEigensystem K ℂ` indexed by $\iota$, subject to four hypotheses. `hb`: for every $i$, $\mathrm{cls}(i)$ lies in `cuspClasses K pins ξK N SK` (level $N$, vanishing $a_v$ and $b_v$ for $v \in S_K$, non-trivial isotypic cusp submodule) and $b_i$ lies in the intersection of `isotypicCuspSubmodule K pins ξK N SK (cls i)` with `archCutSubmodule K tysK`. `hbn` and `hbo`: the $b_i$ are orthonormal for the pairing $\int_D b_i\,\overline{b_j}\,d(\mathtt{adelicGLHaar})$, this integral being $1$ for $i=j$ and $0$ for $i \neq j$. `hbs`: for every cusp class $\pi$ in `cuspClasses K pins ξK N SK`, the set $\{i \mid \mathrm{cls}(i)=\pi\}$ is finite and the complex span of the corresponding $b_i$ equals the intersection of the isotypic cusp submodule of $\pi$ with `archCutSubmodule K tysK`. `hbc`: every $\varphi : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ which is a smooth cuspidal automorphic function at pins for $\xi_K$ (`IsSmoothCuspAutomorphicFnAt`), is continuous, is right invariant under the level subgroup $\mathrm{pins}.U(N)$, lies in `archCutSubmodule K tysK`, and satisfies $\int_D \varphi\,\overline{b_i} = 0$ for all $i$, vanishes almost everywhere for Haar measure restricted to $D$.
--
--   Character pairs for the continuous spectrum: a countable type $\iota_E$ and families $\mu,\nu : \iota_E \to ((\mathbb{A}_K)^\times \to^* \mathbb{C}^\times)$ subject to: unitarity of each $\mu_e$ and each $\nu_e$ in the sense $\lVert\chi(x)\rVert=1$; triviality of each on the principal ideles (`IsIdeleClassChar`); continuity of each; the product relation $\mu_e(z)\,\nu_e(z) = \xi_K(z)$ for all $e$ and all $z$; and the separation hypothesis that for $e \neq e'$ there is a norm-one idele $z$ (an element of [`NumberField.TateGlobal.normOneIdeles K`](def/NumberField_TateGlobalZeta.html#L16), the kernel of the distributive Haar character) at which $\mu_e$ and $\mu_{e'}$, or $\nu_e$ and $\nu_{e'}$, differ.
--
--   Flat section families: natural numbers $n_E(e)$ and functions $\varphi_{e,j} : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ for $j < n_E(e)$, subject to twelve hypotheses: each $\varphi_{e,j}(s)$ is an induced section for the pair $(\mathtt{etaFst}\,\mu_e\,\alpha_m\,h\,s,\ \mathtt{etaSnd}\,\nu_e\,\alpha_m\,h\,s)$, i.e. transforms under left multiplication by an adelic Borel element $b$ by the product of these two characters evaluated at the diagonal entries of $b$; each $\varphi_{e,j}(s)$ is archimedean $K$-finite and $K_f$-smooth; $(s,g) \mapsto \varphi_{e,j}(s)(g)$ is jointly continuous and $s \mapsto \varphi_{e,j}(s)(g)$ is entire; for each infinite place $w$ there is a finite-dimensional subspace $W$ of functions on `archRowIsometrySubgroup K w` containing all right translates $k \mapsto \varphi_{e,j}(s)(gk)$, uniformly in $s$ and $g$; flatness, $\varphi_{e,j}(s)(k)=\varphi_{e,j}(0)(k)$ for $k$ in the adelic maximal compact subgroup; right invariance under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`; membership in `archCutSubmodule K tysK` for each $s$; orthonormality on the maximal compact subgroup, $\int \varphi_{e,i}(0)(k)\,\overline{\varphi_{e,j}(0)(k)}\,d(\mathtt{maximalCompactHaar}) = \delta_{ij}$; and completeness on the imaginary axis: for each real $t$, every continuous, archimedean $K$-finite, level-$N$-invariant section of type $\mathrm{tys}_K$ induced from the pair at $s = it$ lies in the span of the $\varphi_{e,j}(it)$, $j < n_E(e)$. A further hypothesis `_hpairs` exhausts the pairs: for any two continuous unitary idele class characters $\mu',\nu'$ with $\mu'\nu' = \xi_K$, any real $t$ and any non-zero continuous, archimedean $K$-finite, level-$N$-invariant section of type $\mathrm{tys}_K$ induced from $(\mathtt{etaFst}\,\mu'\,\alpha_m\,h\,(it),\ \mathtt{etaSnd}\,\nu'\,\alpha_m\,h\,(it))$, there is $e \in \iota_E$ with $\mu_e = \mu'$ and $\nu_e = \nu'$ on the norm-one ideles.
--
--   Continuations: sets $O_{e,j} \subseteq \mathbb{C}$ and families $E_{e,j}, N_{e,j} : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$, subject to `_hEE`, a conjunction of nine clauses: $O_{e,j}$ is open and preconnected and contains both the imaginary axis $\{\mathrm{Re}\,s = 0\}$ and the half-plane $\{\mathrm{Re}\,s > 1/2\}$; for each $g$ the functions $s \mapsto E_{e,j}(s)(g)$ and $s \mapsto N_{e,j}(s)(g)$ are analytic on a neighbourhood of $O_{e,j}$; both $(s,g)\mapsto E_{e,j}(s)(g)$ and $(s,g)\mapsto N_{e,j}(s)(g)$ are continuous on $O_{e,j}\times\mathrm{GL}_2(\mathbb{A}_K)$; for $\mathrm{Re}\,s>1/2$ and all $g$,
--   $$E_{e,j}(s)(g) = \varphi_{e,j}(s)(g) + \sum_{\xi \in K} \varphi_{e,j}(s)\bigl(w\,u(\xi)\,g\bigr),$$
--   with $w = \mathtt{adelicWeyl}$ and $u(\xi)$ the unipotent matrix with upper entry the image of $\xi$; and for $\mathrm{Re}\,s>1/2$ and all $g$, $N_{e,j}(s)(g)$ equals the Weyl intertwining integral $\int_{\mathbb{A}_K} \varphi_{e,j}(s)(w^{-1}u(x)g)\,dx$ for additive adelic Haar measure.
--
--   Test function: a function $u : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ satisfying `IsAutomorphicFnAt K pins ξK u`, that is, the condition `LsXiMember` for the Haar measure, the domain $D$, the full central subgroup and $\xi_K$ recorded in the pins, and satisfying `_hub`: there is a real $T$ such that $u(g)=0$ for every $g \in D$ with $\mathtt{adelicHeight}\,K\,g > T$, the adelic height being the product of the archimedean height of the archimedean part and the finite height of the finite part.
--
--   Finally, indices $e \in \iota_E$ and $j < n_E(e)$ are fixed.
--
--   The conclusion is a conjunction of two assertions about the Eisenstein coefficient
--   $$\Theta(t) := \int_D u(g)\,\overline{E_{e,j}(it)(g)}\,d(\mathtt{adelicGLHaar}\,(\mathrm{Fin}\,2)\,(\mathcal{O}_K)\,K).$$
--   First, the function $t \mapsto \Theta(t)$ is continuous on $\mathbb{R}$. Second, there exist a real $A$ and a natural number $k$ such that $\lVert \Theta(t)\rVert \le A\,(1+|t|)^k$ for every $t \in \mathbb{R}$.
--
--   This is the regularity statement for the coefficients of a height-truncated automorphic function against the analytic continuation of the Eisenstein series along the unitary axis: continuity in the spectral parameter together with polynomial growth. It is used in the proof of the Weyl-intertwining pairing identity [`AutomorphicForm.sum_integral_sum_conj_inner_weylIntertwining_mul_setIntegral_mul_conj_axis_continuation_eq_of_isAutomorphicFnAt_of_lt_adelicHeight`](thm.html#AutomorphicForm.sum_integral_sum_conj_inner_weylIntertwining_mul_setIntegral_mul_conj_axis_continuation_eq_of_isAutomorphicFnAt_of_lt_adelicHeight), where these bounds licence the integration against the continuous spectrum in the spectral decomposition of the truncated space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuous_setIntegral_mul_conj_axis_continuation_and_exists_norm_le_mul_one_add_abs_pow_of_isAutomorphicFnAt_of_lt_adelicHeight.lean

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

theorem AutomorphicForm.continuous_setIntegral_mul_conj_axis_continuation_and_exists_norm_le_mul_one_add_abs_pow_of_isAutomorphicFnAt_of_lt_adelicHeight
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
      (u : AdelicGL2 (𝓞 K) K → ℂ)
      (_hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u)
      (_hub : ∃ T : ℝ, ∀ g ∈ AutomorphicForm.canonicalTruncationDomain K α β,
        T < NumberField.AdelicHeight.adelicHeight K g → u g = 0)
      (e : ιE) (j : Fin (nE e)),
    (Continuous fun t : ℝ => ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, u g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    ∃ (A : ℝ) (k : ℕ), ∀ t : ℝ, ‖∫ g in AutomorphicForm.canonicalTruncationDomain K α β, u g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)‖ ≤ A * (1 + |t|) ^ k := by sorry
