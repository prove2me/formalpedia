-- Prove2me | Theorems.Thm_AutomorphicForm_exists_partner_forall_partner_partner_eq_and_eq_mul_normPowChar_of_pairs_complete
-- name    : AutomorphicForm.exists_partner_forall_partner_partner_eq_and_eq_mul_normPowChar_of_pairs_complete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/c700de52-08d0-5a34-ab0f-fe9a8c4ceb0e
-- title:
--   Swap partners with norm-power twist for complete Eisenstein families
-- statement:
--   Throughout, $K$ is a number field, and $\alpha,\beta$ are reals with $0<\alpha<\beta$; the associated truncation region is [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32), the second component of the canonically chosen truncation datum for $(\alpha,\beta)$. A set `ΦK` of adelic matrices is among the parameters and occurs in no other hypothesis and not in the conclusion.
--
--   *Siegel covering data.* Reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}<d_{2K}$ and a finite set $T_K\subseteq \mathrm{GL}_2(\mathbb{A}_K)$ are given such that `hcovK` holds: the union $\bigcup_{x\in T_K}(\cdot\,x)''\,\mathrm{centreCutSiegelSet}\,K\,c_K\,u_K\,d_{1K}\,d_{2K}$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo $\mathrm{GL}_2(K)$ and the centre, i.e. for every $g$ there are $\gamma\in \mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g\,z\cdot 1$ in that union. Here the centre-cut Siegel set consists of those $g$ whose finite component lies in `finiteIntegralGL2`, and which at every infinite place $w$ satisfy $c_K\le \mathrm{localHeight}$, $\mathrm{xWindowSq}\le u_K^2$ and $\mathrm{archDetNorm}_w(g)\in[d_{1K},d_{2K}]$.
--
--   *Central data.* A Haar measure $\nu_{ZK}$ on the idele group $\mathbb{A}_K^\times$ (with its measurable and Borel structures) and a set $\Omega_K$ which, by `hΩK`, is a fundamental domain for the image of $K^\times$ in $\mathbb{A}_K^\times$ with respect to $\nu_{ZK}$. A finite set $S_K$ of finite places of $K$, a character $\xi_K$ of the full subgroup $\top\le\mathbb{A}_K^\times$ with values in $\mathbb{C}^\times$ which is continuous (`hξc`), trivial on the image of $K^\times$ (`hξt`) and unitary, $\lVert\xi_K(z)\rVert=1$ for all $z$ (`hξu`). An ideal $N$ of $\mathcal{O}_K$ such that every finite place $v$ with $v\mid N$ belongs to $S_K$ (`hN`), and a family `tysK : ArchTypeFamily K` of finitely many archimedean representation types at each infinite place, whose associated space `archCutSubmodule K tysK` is the intersection over infinite places $w$ of the sum of the type subspaces for the chosen types at $w$.
--
--   The modulus character $\alpha_m:\mathbb{A}_K^\times\to\mathbb{R}^\times$ is the unit-group homomorphism induced by the distributive Haar character of the adele ring composed with $\mathbb{R}_{\ge 0}\to\mathbb{R}$, and the Borel structure on $\mathbb{A}_K$ is the one of `adeleBorel`; the hypothesis `hαm` asserts $\alpha_m(x)>0$ for all $x$. All carrier data are packaged in the pins $\mathrm{pins}=$ `productionPinsOf K (canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, domain the truncation region, central subgroup $\top$, level subgroups $M\mapsto \mathrm{principalLevel}(M)\sqcap\mathrm{finiteAdelicGL2Subgroup}$, Hecke generators `heckeGen`, and on $\mathbb{A}_K$ the Haar measure conditioned on `adelicBox K`.
--
--   *Cuspidal spectral data.* An index type $\iota$, functions $b:\iota\to(\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ and $\mathrm{cls}:\iota\to$ `HeckeEigensystem K ℂ` (a level ideal, nonzero, together with eigenvalue functions $a,b$ on finite places), subject to: `hb`, each $\mathrm{cls}\,i$ lies in `cuspClasses` for $\mathrm{pins},\xi_K,N,S_K$ (level $N$, vanishing of $a_v$ and $b_v$ for $v\in S_K$, nonzero isotypic cusp space) and $b\,i$ lies in the isotypic cusp submodule of $\mathrm{cls}\,i$ intersected with `archCutSubmodule K tysK`; `hbn`, $\int_{D} b_i\overline{b_i}=1$ over the truncation domain $D$ for the adelic Haar measure; `hbo`, $\int_D b_i\overline{b_j}=0$ for $i\ne j$; `hbs`, for every class $\pi$ in `cuspClasses` the fibre $\{i\mid \mathrm{cls}\,i=\pi\}$ is finite and the $\mathbb{C}$-span of its image under $b$ is exactly the isotypic cusp submodule of $\pi$ intersected with the archimedean type space; and `hbc`, completeness: any $\varphi$ which is a smooth cuspidal automorphic function for $\mathrm{pins}$ and $\xi_K$, is continuous, is invariant under right translation by $\mathrm{pins}.U\,N$, lies in the archimedean type space, and is orthogonal over $D$ to every $b_i$, vanishes almost everywhere on $D$.
--
--   *Continuous-spectrum data.* A countable index type $\iota_E$ and families $\mu,\nu:\iota_E\to(\mathbb{A}_K^\times\to\mathbb{C}^\times)$ with: each $\mu_e,\nu_e$ unitary (`_hμ`, `_hν`), trivial on $K^\times$ (`_hμic`, `_hνic`), continuous (`_hμc`, `_hνc`), satisfying $\mu_e\nu_e=\xi_K$ pointwise (`_hμν`), and separated: for $e\ne e'$ some norm-one idele $z$ has $\mu_e(z)\ne\mu_{e'}(z)$ or $\nu_e(z)\ne\nu_{e'}(z)$ (`_hdist`).
--
--   *Flat sections.* Numbers $n_E(e)\in\mathbb{N}$ and functions $\varphi_{e,j}:\mathbb{C}\to(\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ for $j<n_E(e)$, subject to the following hypotheses, each asserted for all $e$, $j$ and all $s$ where applicable: `_hφE`, $\varphi_{e,j}(s)$ is an induced section for the pair $\bigl(\mu_e\,\alpha_m^{s+1/2},\ \nu_e\,\alpha_m^{-(s+1/2)}\bigr)$, i.e. $\varphi(bg)=\chi_1(b_{11})\chi_2(b_{22})\varphi(g)$ for $b$ in the adelic Borel subgroup; `_hφEK`, archimedean $\mathbf{K}$-finiteness at every infinite place; `_hφEf`, smoothness along the finite adelic subgroup; `_hφEjc`, joint continuity in $(s,g)$; `_hφEhol`, holomorphy in $s$ for fixed $g$; `_hφEKu`, for each infinite place a finite-dimensional space of functions on the archimedean row-isometry subgroup containing all right translates $k\mapsto\varphi_{e,j}(s)(gk)$; `_hφEflat`, flatness, $\varphi_{e,j}(s)(k)=\varphi_{e,j}(0)(k)$ for $k$ in the adelic maximal compact; `_hφElev`, right invariance under $\mathrm{principalLevel}(N)\sqcap\mathrm{finiteAdelicGL2Subgroup}$; `_hφEty`, membership in `archCutSubmodule K tysK`; `_hφEon`, orthonormality of $\varphi_{e,i}(0),\varphi_{e,j}(0)$ on the adelic maximal compact for `maximalCompactHaar K`; and `_hφEspan`, spanning on the unitary axis: for every real $t$, every section $\varphi_0$ induced from $(\mu_e,\nu_e)$ at $s=it$ which is continuous, archimedean $\mathbf{K}$-finite, right invariant under the level group and of the given archimedean types lies in the $\mathbb{C}$-span of the $\varphi_{e,j}(it)$, $j<n_E(e)$.
--
--   *Completeness for pairs.* The hypothesis `_hpairs`: for every pair $(\mu',\nu')$ of continuous unitary characters of $\mathbb{A}_K^\times$ trivial on $K^\times$ with $\mu'\nu'=\xi_K$, every real $t$ and every nonzero $\varphi_0$ which is an induced section for $\bigl(\mu'\alpha_m^{it+1/2},\nu'\alpha_m^{-(it+1/2)}\bigr)$, continuous, archimedean $\mathbf{K}$-finite, right invariant under $\mathrm{principalLevel}(N)\sqcap\mathrm{finiteAdelicGL2Subgroup}$ and of the given archimedean types, there exists $e\in\iota_E$ with $\mu_e(z)=\mu'(z)$ and $\nu_e(z)=\nu'(z)$ for every norm-one idele $z$.
--
--   *Axis continuations.* Sets $O_{e,j}\subseteq\mathbb{C}$ and functions $E_{e,j},N_{e,j}:\mathbb{C}\to(\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ with `_hEE`: each $O_{e,j}$ is open and preconnected and contains both the line $\{\operatorname{Re}s=0\}$ and the half-plane $\{\operatorname{Re}s>1/2\}$; for each $g$ the functions $s\mapsto E_{e,j}(s)(g)$ and $s\mapsto N_{e,j}(s)(g)$ are analytic on a neighbourhood of $O_{e,j}$; both are continuous on $O_{e,j}\times\mathrm{univ}$; for $\operatorname{Re}s>1/2$ one has the Eisenstein expansion $E_{e,j}(s)(g)=\varphi_{e,j}(s)(g)+\sum_{\xi\in K}\varphi_{e,j}(s)\bigl(w\,u(\xi)\,g\bigr)$ with $w=$ `adelicWeyl` and $u(\xi)$ the unipotent matrix with entry the image of $\xi$, and $N_{e,j}(s)(g)=$ `weylIntertwiningIntegral` of $\varphi_{e,j}(s)$ at $g$, taken with the adelic additive Haar measure.
--
--   *Conclusion.* Under these hypotheses there exist a map $\mathrm{prt}:\iota_E\to\iota_E$ and a function $\sigma:\iota_E\to\mathbb{R}$ such that for every $e\in\iota_E$ with $n_E(e)>0$ the following three statements hold: $\mathrm{prt}(\mathrm{prt}\,e)=e$; $\mu_{\mathrm{prt}\,e}=\nu_e\cdot\mathrm{normPowChar}_K(\sigma(e))$; and $\nu_{\mathrm{prt}\,e}=\mu_e\cdot\mathrm{normPowChar}_K(\sigma(e))^{-1}$. Here $\mathrm{normPowChar}_K(t)$ is the character $x\mapsto \lVert x\rVert^{\,it}$ built from the idele norm, and the two identities are equalities of homomorphisms on the whole idele group, not merely on the norm-one ideles.
--
--   This is the symmetry of an Eisenstein datum index set under interchange of the two inducing characters: each pair $(\mu_e,\nu_e)$ carrying sections is matched involutively with the swapped pair, up to a purely imaginary power of the idele norm, which is the bookkeeping underlying the functional equation of the $\mathrm{GL}_2$ Eisenstein series. It feeds the spectral-decomposition step [`AutomorphicForm.exists_matched_paleyWiener_injective_and_inner_eq_integral_mul_cexp_and_sum_integral_sum_conj_inner_mul_eq_and_setIntegral_normSq_sub_residualProj_le_of_contDiff_hasCompactSupport`](thm.html#AutomorphicForm.exists_matched_paleyWiener_injective_and_inner_eq_integral_mul_cexp_and_sum_integral_sum_conj_inner_mul_eq_and_setIntegral_normSq_sub_residualProj_le_of_contDiff_hasCompactSupport), where the continuous part of the Plancherel formula is matched pair by pair.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_partner_forall_partner_partner_eq_and_eq_mul_normPowChar_of_pairs_complete.lean

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

open scoped ContDiff

theorem AutomorphicForm.exists_partner_forall_partner_partner_eq_and_eq_mul_normPowChar_of_pairs_complete
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
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g)),
    ∃ (prt : ιE → ιE) (σ : ιE → ℝ), ∀ e : ιE, 0 < nE e →
      prt (prt e) = e ∧
      μ (prt e) = ν e * NumberField.TateGlobal.normPowChar K (σ e) ∧
      ν (prt e) = μ e * (NumberField.TateGlobal.normPowChar K (σ e))⁻¹ := by sorry
