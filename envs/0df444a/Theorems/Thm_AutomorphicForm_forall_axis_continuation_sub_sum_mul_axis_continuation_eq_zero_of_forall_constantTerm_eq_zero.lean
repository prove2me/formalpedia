-- Prove2me | Theorems.Thm_AutomorphicForm_forall_axis_continuation_sub_sum_mul_axis_continuation_eq_zero_of_forall_constantTerm_eq_zero
-- name    : AutomorphicForm.forall_axis_continuation_sub_sum_mul_axis_continuation_eq_zero_of_forall_constantTerm_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/8a7c933e-ccdb-555c-921b-878de026f45d
-- title:
--   Vanishing of axis Eisenstein combinations with zero constant term
-- statement:
--   Fix a number field $K$ and real numbers $\alpha,\beta$ with $0<\alpha$ and $\alpha<\beta$; write $\Phi_0=$ [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) for the canonical truncation domain attached to the slab $\alpha\le\|\det g\|\le\beta$, and let $\mathbb{A}=$ `AdeleRing (𝓞 K) K`.
--
--   *Geometric and measure-theoretic data.* A set $\Phi_K$ of adelic points of $\mathrm{GL}_2$ is among the data, with no condition imposed on it. Real parameters $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}$, $d_{1K}<d_{2K}$ and a finite set $T_K\subseteq\mathrm{GL}_2(\mathbb{A})$ are given, subject to `hcovK`: the union $\bigcup_{x\in T_K}(\cdot\,x)''\,$`centreCutSiegelSet K cK uK d₁K d₂K` covers $\mathrm{GL}_2(\mathbb{A})$ modulo the centre, i.e. for every $g$ there are $\gamma\in\mathrm{GL}_2(K)$ and a central idele $z$ with $\gamma g z$ in that union; here the centre-cut Siegel set consists of those $g$ whose finite part is integral, whose archimedean local heights at every infinite place are $\ge c_K$, whose window quantities `xWindowSq` are $\le u_K^2$, and whose archimedean determinant norms lie in $[d_{1K},d_{2K}]$. Further, the idele unit group $\mathbb{A}^\times$ carries a measurable structure which is its Borel structure, $\nu_{ZK}$ is a Haar measure on it, and $\Omega_K$ is, by `hΩK`, a fundamental domain for the subgroup of principal ideles (the range of $K^\times\to\mathbb{A}^\times$) with respect to $\nu_{ZK}$.
--
--   *Central character, level and types.* $S_K$ is a finite set of finite places; $\xi_K$ is a homomorphism from the full subgroup $\top\le\mathbb{A}^\times$ to $\mathbb{C}^\times$ which is continuous (`hξc`), trivial on principal ideles (`hξt`) and unitary, $\|\xi_K(z)\|=1$ (`hξu`); $N$ is an ideal of $\mathcal{O}_K$ such that every place dividing $N$ lies in $S_K$ (`hN`); and `tysK` is a family of archimedean types, i.e. for each infinite place $w$ a finite list of representations of the row-isometry group of $K_w$, cutting out the submodule `archCutSubmodule K tysK` $=\bigsqcap_w\bigsqcup_i$ `archTypeSubmoduleAt`. Throughout, `pins` abbreviates `productionPinsOf K Φ₀ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: the carrier data with Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` on $\mathrm{GL}_2(\mathbb{A})$, domain $\Phi_0$, central subgroup $\top$, level subgroups $\Gamma(M)\cap\mathrm{GL}_2(\mathbb{A}_f)$, Hecke generators `heckeGen`, and the conditional additive Haar measure of $\mathbb{A}$ on the box `adelicBox K`.
--
--   Let $\alpha_m:\mathbb{A}^\times\to\mathbb{R}^\times$ be the unit-group homomorphism induced by the distributive Haar character of $\mathbb{A}$ composed with $\mathbb{R}_{\ge0}\to\mathbb{R}$, and let `hαm` assert $\alpha_m(x)>0$ for all $x$. Adele-ring measurability is the Borel structure `adeleBorel`.
--
--   *Cusp basis.* An index type $\iota$, functions $b_i:\mathrm{GL}_2(\mathbb{A})\to\mathbb{C}$ and Hecke eigensystems $\mathrm{cls}(i)\in$ `HeckeEigensystem K ℂ` are given with: `hb`, each $\mathrm{cls}(i)$ lies in `cuspClasses K pins ξK N SK` (level $=N$, $a_v=b_v=0$ for $v\in S_K$, and non-zero isotypic cusp submodule) and $b_i\in$ `isotypicCuspSubmodule K pins ξK N SK (cls i)` $\sqcap$ `archCutSubmodule K tysK`, the isotypic submodule being the $\mathbb{C}$-span of the smooth cuspidal automorphic functions of central character $\xi_K$ which are continuous, right invariant under $\Gamma(N)\cap\mathrm{GL}_2(\mathbb{A}_f)$ and Hecke/central eigenfunctions outside $S_K$ with the eigenvalues prescribed by the eigensystem; `hbn`, $\int_{\Phi_0}b_i\overline{b_i}=1$; `hbo`, $\int_{\Phi_0}b_i\overline{b_j}=0$ for $i\ne j$, both integrals taken against `adelicGLHaar (Fin 2) (𝓞 K) K`; `hbs`, for every $\pi$ in `cuspClasses K pins ξK N SK` the fibre $\{i\mid \mathrm{cls}(i)=\pi\}$ is finite and the span of the corresponding $b_i$ is exactly the $\pi$-isotypic cusp submodule intersected with the type cut; and `hbc`, the completeness clause: any $\varphi$ which is a smooth cuspidal automorphic function for `pins` and $\xi_K$, continuous, right invariant under the level subgroup `pins.U N`, lies in `archCutSubmodule K tysK` and satisfies $\int_{\Phi_0}\varphi\overline{b_i}=0$ for all $i$, vanishes almost everywhere for `adelicGLHaar (Fin 2) (𝓞 K) K` restricted to $\Phi_0$.
--
--   *Family of induced sections.* A countable type $\iota_E$ and families of characters $\mu,\nu:\iota_E\to(\mathbb{A}^\times\to\mathbb{C}^\times)$ are given with the hypotheses `_hμ`, `_hν` (unitarity), `_hμic`, `_hνic` (triviality on $K^\times$), `_hμc`, `_hνc` (continuity), `_hμν` ($\mu_e\nu_e=\xi_K$ pointwise) and `_hdist` (for $e\ne e'$ some norm-one idele separates $\mu_e$ from $\mu_{e'}$ or $\nu_e$ from $\nu_{e'}$). For each $e$ there are $n_E(e)\in\mathbb{N}$ and functions $\varphi_{e,j}:\mathbb{C}\times\mathrm{GL}_2(\mathbb{A})\to\mathbb{C}$, $j<n_E(e)$, satisfying the following clauses (all summarised, none omitted): `_hφE`, for every $s$ the function $\varphi_{e,j}(s,\cdot)$ is an induced section for the pair `etaFst (μ e) αm hαm s` $=\mu_e\cdot\alpha_m^{\,s+1/2}$ and `etaSnd (ν e) αm hαm s` $=\nu_e\cdot\alpha_m^{-(s+1/2)}$, i.e. $\varphi(bg)$ equals the product of the two characters evaluated on the diagonal entries of the upper-triangular $b$ times $\varphi(g)$; `_hφEK`, archimedean $K$-finiteness at every infinite place; `_hφEf`, $K_f$-smoothness; `_hφEjc`, joint continuity in $(s,g)$; `_hφEhol`, holomorphy in $s$ for fixed $g$; `_hφEKu`, a single finite-dimensional space $W$ of functions on the archimedean row-isometry subgroup at each $w$ containing all right translates; `_hφEflat`, flatness on the maximal compact, $\varphi_{e,j}(s,k)=\varphi_{e,j}(0,k)$ for $k\in$ `adelicMaximalCompact K`; `_hφElev`, right invariance under $\Gamma(N)\cap\mathrm{GL}_2(\mathbb{A}_f)$; `_hφEty`, membership in the type cut `archCutSubmodule K tysK` for every $s$; `_hφEon`, orthonormality $\int_{\mathrm{adelicMaximalCompact}\,K}\varphi_{e,i}(0,k)\overline{\varphi_{e,j}(0,k)}\,d(\mathrm{maximalCompactHaar}\,K)=\delta_{ij}$; `_hφEspan`, for every $t\in\mathbb{R}$, every induced section $\varphi_0$ at $s=it$ for the pair attached to $(\mu_e,\nu_e)$ which is continuous, archimedean $K$-finite, level-$N$ invariant and of the prescribed types lies in the $\mathbb{C}$-span of the $\varphi_{e,j}(it,\cdot)$; and `_hpairs`, exhaustiveness: any pair $(\mu',\nu')$ of continuous unitary idele-class characters with $\mu'\nu'=\xi_K$ which admits a non-zero such section at some point $it$ agrees with some $(\mu_e,\nu_e)$ on the norm-one ideles.
--
--   *Continuations.* Sets $O_{e,j}\subseteq\mathbb{C}$ and functions $E_{e,j},N_{e,j}:\mathbb{C}\times\mathrm{GL}_2(\mathbb{A})\to\mathbb{C}$ are given such that, by `_hEE`, each $O_{e,j}$ is open and preconnected, contains the imaginary axis $\{\operatorname{Re}s=0\}$ and the half-plane $\{\operatorname{Re}s>1/2\}$; for each $g$ both $s\mapsto E_{e,j}(s,g)$ and $s\mapsto N_{e,j}(s,g)$ are analytic on a neighbourhood of $O_{e,j}$; both are continuous on $O_{e,j}\times\mathrm{GL}_2(\mathbb{A})$ jointly; for $\operatorname{Re}s>1/2$ one has the Bruhat expansion $E_{e,j}(s,g)=\varphi_{e,j}(s,g)+\sum_{\xi\in K}\varphi_{e,j}\bigl(s,\,w\,u(\xi)\,g\bigr)$ with $w=$ `adelicWeyl` and $u(\xi)=$ `unipotentGL2` of the image of $\xi$; and for $\operatorname{Re}s>1/2$, $N_{e,j}(s,g)$ is the Weyl intertwining integral $\int_{\mathbb{A}}\varphi_{e,j}(s,w^{-1}u(x)g)\,dx$ against `adelicAddHaar`.
--
--   *Swap and the combination.* Indices $e,\bar e\in\iota_E$ and $\sigma\in\mathbb{R}$ are given with `_hsw`: $\mu_{\bar e}=\nu_e\cdot$ `normPowChar K σ` and $\nu_{\bar e}=\mu_e\cdot($ `normPowChar K σ` $)^{-1}$. Finally $j<n_E(e)$, $t\in\mathbb{R}$, coefficients $c_{j'}\in\mathbb{C}$ for $j'<n_E(\bar e)$, and $g\in\mathrm{GL}_2(\mathbb{A})$ are given, subject to `_hCT`: the constant term of the function
--   $$D(x)=E_{e,j}(it,x)-\sum_{j'<n_E(\bar e)}c_{j'}E_{\bar e,j'}\bigl(-i(t+\sigma),x\bigr)$$
--   along the unipotent embedding $u\mapsto$ `unipotentGL2 u`, taken with respect to the conditional measure of `adelicAddHaar (𝓞 K) K` on `adelicBox K`, vanishes at every point: $\int D(u(q)\,x)\,dq=0$ for all $x$.
--
--   The conclusion is that
--   $$E_{e,j}(it,g)-\sum_{j'<n_E(\bar e)}c_{j'}E_{\bar e,j'}\bigl(-i(t+\sigma),g\bigr)=0,$$
--   that is, $D(g)=0$ for the (arbitrary) point $g$.
--
--   This is Langlands' vanishing principle on the unitary axis in the form needed for the continuous part of the spectral decomposition: a finite combination of analytically continued Bruhat–Eisenstein values whose constant term vanishes identically is a cuspidal function orthogonal to a complete orthonormal cusp basis, hence zero. It is the step used by [`AutomorphicForm.axis_continuation_eq_sum_inner_weylIntertwining_mul_axis_continuation_of_swap_normPowChar`](thm.html#AutomorphicForm.axis_continuation_eq_sum_inner_weylIntertwining_mul_axis_continuation_of_swap_normPowChar) to identify an axis Eisenstein value with the corresponding combination of intertwined values, i.e. to obtain the functional equation on the line $\operatorname{Re}s=0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_forall_axis_continuation_sub_sum_mul_axis_continuation_eq_zero_of_forall_constantTerm_eq_zero.lean

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

theorem AutomorphicForm.forall_axis_continuation_sub_sum_mul_axis_continuation_eq_zero_of_forall_constantTerm_eq_zero
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
      (e ē : ιE) (σ : ℝ)
      (_hsw : μ ē = ν e * NumberField.TateGlobal.normPowChar K σ ∧
        ν ē = μ e * (NumberField.TateGlobal.normPowChar K σ)⁻¹)
      (j : Fin (nE e)) (t : ℝ) (c : Fin (nE ē) → ℂ)
      (_hCT : ∀ g : AdelicGL2 (𝓞 K) K,
        AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
          (fun u => AutomorphicForm.unipotentGL2 u)
          (fun x : AdelicGL2 (𝓞 K) K => (EE e j ((t : ℂ) * Complex.I) x -
          ∑ j' : Fin (nE ē), c j' * EE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) x)) g = 0)
      (g : AdelicGL2 (𝓞 K) K),
    (EE e j ((t : ℂ) * Complex.I) g -
          ∑ j' : Fin (nE ē), c j' * EE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) g) = 0 := by sorry
