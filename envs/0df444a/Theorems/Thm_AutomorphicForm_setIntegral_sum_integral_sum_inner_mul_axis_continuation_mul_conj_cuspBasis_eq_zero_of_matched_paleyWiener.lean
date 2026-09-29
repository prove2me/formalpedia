-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_sum_integral_sum_inner_mul_axis_continuation_mul_conj_cuspBasis_eq_zero_of_matched_paleyWiener
-- name    : AutomorphicForm.setIntegral_sum_integral_sum_inner_mul_axis_continuation_mul_conj_cuspBasis_eq_zero_of_matched_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/b1203b16-fcf4-5be7-a5af-1ac91072dda2
-- title:
--   Orthogonality of matched wave packets to the cusp basis
-- statement:
--   Throughout, $K$ is a number field, $\mathbb{A}_K$ its adele ring and $\mathrm{AdelicGL2}$ denotes $\mathrm{GL}_2(\mathbb{A}_K)$. Real parameters $\alpha,\beta$ with $0<\alpha$ and $\alpha<\beta$ fix the norm slab and the canonical truncation domain [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32), the distinguished fundamental-domain component produced by the canonical truncation datum; all integrals over $\mathrm{GL}_2(\mathbb{A}_K)$ are taken against the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` for the Borel $\sigma$-algebra.
--
--   Geometric and measure-theoretic data. A set $\Phi_K\subseteq\mathrm{GL}_2(\mathbb{A}_K)$ occurs as a binder with no condition imposed on it. Reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}<d_{2K}$ and a finite set $T_K\subseteq\mathrm{GL}_2(\mathbb{A}_K)$ satisfy `hcovK`: the union over $x\in T_K$ of the right translates by $x$ of the centre-cut Siegel set (matrices whose finite part is integral, whose local height at every infinite place is at least $c_K$, whose $x$-window square at every infinite place is at most $u_K^2$, and whose archimedean determinant norms all lie in $[d_{1K},d_{2K}]$) covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo $\mathrm{GL}_2(K)$ on the left and the adelic centre on the right. Furthermore $\nu_{Z,K}$ is a Haar measure on the idele group $\mathbb{A}_K^\times$ and $\Omega_K$ is, by `hΩK`, a fundamental domain for the image of $K^\times$ in $\mathbb{A}_K^\times$ with respect to $\nu_{Z,K}$.
--
--   Arithmetic data. $S_K$ is a finite set of finite places; $\xi_K$ is a homomorphism from the full subgroup $\top\le\mathbb{A}_K^\times$ to $\mathbb{C}^\times$ which is continuous (`hξc`), trivial on the principal ideles (`hξt`) and unitary (`hξu`); $N$ is an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$ (`hN`); and $\mathcal{T}_K$ is an archimedean type family, i.e. for each infinite place $w$ a finite list of representations of the row-isometry group at $w$, cutting out the submodule `archCutSubmodule K tysK` (the intersection over $w$ of the sums of the corresponding type submodules). The character $\alpha_m:\mathbb{A}_K^\times\to\mathbb{R}^\times$ is the module character, the unit-group homomorphism attached to `distribHaarChar (AdeleRing (𝓞 K) K)` followed by the inclusion $\mathbb{R}_{\ge0}\to\mathbb{R}$, and `hαm` asserts its positivity. The carrier `productionPinsOf K (canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)` is used throughout: Borel $\sigma$-algebra and Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, domain the canonical truncation domain, central subgroup $\top$, level subgroups $\Gamma(M)\cap\ker(\mathrm{GL}_2(\mathbb{A}_K)\to\mathrm{GL}_2(\mathbb{A}_{K,\infty}))$, Hecke generators $\mathrm{heckeGen}_v$, and the additive Haar measure on $\mathbb{A}_K$ conditioned on the adelic box.
--
--   Cuspidal basis. A type $\iota$, functions $b_i:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ and Hecke eigensystems $\mathrm{cls}(i)$ are given with: `hb`, each $\mathrm{cls}(i)$ is a cusp class for the above pins, $\xi_K$, $N$, $S_K$ (level $N$, vanishing $a_v,b_v$ for $v\in S_K$, nonzero isotypic cuspidal submodule) and $b_i$ lies in the intersection of the isotypic cuspidal submodule of $\mathrm{cls}(i)$ with the archimedean cut submodule; `hbn`, $\int_{\Phi_0}b_i\overline{b_i}=1$; `hbo`, $\int_{\Phi_0}b_i\overline{b_j}=0$ for $i\neq j$, where $\Phi_0$ is the canonical truncation domain; `hbs`, for each cusp class $\pi$ the fibre $\{i\mid \mathrm{cls}(i)=\pi\}$ is finite and the $\mathbb{C}$-span of the corresponding $b_i$ is the whole intersection of the isotypic submodule of $\pi$ with the archimedean cut submodule; and `hbc`, completeness: any $\varphi$ which is a smooth cuspidal automorphic function for the pins and $\xi_K$ (automorphic with central character $\xi_K$, cuspidal for the conditioned adelic measure, and $K_f$-smooth), continuous, invariant under right translation by the level group $U(N)$, contained in the archimedean cut submodule and orthogonal on $\Phi_0$ to every $b_i$, vanishes almost everywhere for Haar measure restricted to $\Phi_0$.
--
--   Continuous-spectrum frame. A countable type $\iota_E$ indexes pairs of characters $\mu_e,\nu_e:\mathbb{A}_K^\times\to\mathbb{C}^\times$ which are unitary, trivial on $K^\times$, continuous, satisfy $\mu_e\nu_e=\xi_K$ and are pairwise separated on the norm-one ideles (`_hdist`: distinct $e,e'$ are distinguished by $\mu$ or $\nu$ at some norm-one idele). For each $e$ an integer $n_e$ and functions $\varphi_{e,j}(s,\cdot)$, $j<n_e$, are given, subject to: `_hφE`, each $\varphi_{e,j}(s,\cdot)$ is an induced section for the pair $(\mu_e\,\alpha_m^{s+1/2},\ \nu_e\,\alpha_m^{-(s+1/2)})$, i.e. $\varphi(bg)=\eta_1(b_{00})\eta_2(b_{11})\varphi(g)$ for $b$ in the adelic Borel subgroup; `_hφEK`, archimedean $K$-finiteness; `_hφEf`, $K_f$-smoothness; `_hφEjc`, joint continuity in $(s,g)$; `_hφEhol`, holomorphy in $s$ for each $g$; `_hφEKu`, at each infinite place the right translates along the row-isometry subgroup lie in one finite-dimensional space, uniformly in $s$ and $g$; `_hφEflat`, flatness on the adelic maximal compact subgroup, $\varphi_{e,j}(s,k)=\varphi_{e,j}(0,k)$; `_hφElev`, right invariance under $\Gamma(N)\cap$ the finite-adelic subgroup; `_hφEty`, membership in the archimedean cut submodule; `_hφEon`, orthonormality on the maximal compact subgroup against its Haar measure, $\int_{\mathbf{K}}\varphi_{e,j}(0,k)\overline{\varphi_{e,j'}(0,k)}\,dk=\delta_{jj'}$; `_hφEspan`, on the unitary axis $s=it$ every $\varphi_0$ which is an induced section for the same pair, continuous, archimedean $K$-finite, right $\Gamma(N)$-invariant and of the given archimedean types lies in the span of the $\varphi_{e,j}(it,\cdot)$; and `_hpairs`, exhaustiveness: any pair of continuous unitary idele class characters $\mu',\nu'$ with $\mu'\nu'=\xi_K$ carrying a nonzero such section on the unitary axis agrees with some $(\mu_e,\nu_e)$ on the norm-one ideles. Sets $O_{e,j}\subseteq\mathbb{C}$ and families $E_{e,j}$, $N_{e,j}$ satisfy `_hEE` (eight clauses): $O_{e,j}$ is open and preconnected and contains both the imaginary axis and the half-plane $\mathrm{Re}\,s>1/2$; for each $g$ the functions $s\mapsto E_{e,j}(s,g)$ and $s\mapsto N_{e,j}(s,g)$ are analytic on a neighbourhood of $O_{e,j}$; both are continuous on $O_{e,j}\times\mathrm{GL}_2(\mathbb{A}_K)$ jointly; for $\mathrm{Re}\,s>1/2$ one has $E_{e,j}(s,g)=\varphi_{e,j}(s,g)+\sum'_{\xi\in K}\varphi_{e,j}(s,\,w\,u(\xi)\,g)$ with $w$ the adelic Weyl element and $u(\xi)$ the unipotent matrix; and $N_{e,j}(s,g)$ equals the Weyl intertwining integral $\int_{\mathbb{A}_K}\varphi_{e,j}(s,\,w^{-1}u(x)g)\,dx$.
--
--   Matched Paley–Wiener datum. A finite type $\iota_P$ indexes characters $\mu_{P,e},\nu_{P,e}$ which are unitary, trivial on $K^\times$, continuous (both families), satisfy $\mu_{P,e}(z)\nu_{P,e}(z)=\xi_K(z)$ for $z$ in the central subgroup of the pins, are permuted by an involutive swap $r_P$ with $\mu_{P,r_P e}=\nu_{P,e}$ and $\nu_{P,r_P e}=\mu_{P,e}$, and are pairwise separated on the norm-one ideles. Functions $\hat\psi_e(s,\cdot)$ are induced sections for $(\mu_{P,e}\alpha_m^{s+1/2},\nu_{P,e}\alpha_m^{-(s+1/2)})$, jointly continuous in $(s,g)$, holomorphic in $s$, archimedean $K$-finite, $K_f$-smooth, with finite-dimensional archimedean $K$-type at each infinite place, and vertically rapidly decreasing (`_hψdec`: for each $e$, each $n$, each $\sigma_0$ and each compact $C$ there is an integrable bounded majorant $m$ with $(1+|t|)^n\|\hat\psi_e(\sigma'+it,g)\|\le m(t)$ for $|\sigma'|\le\sigma_0$ and $g\in C$). A function $\psi$ is a slab profile for the central subgroup and $\xi_K$ (`_hψ`: measurable, invariant under left unipotent translation, invariant under left translation by the rational Borel subgroup, transforming by $\xi_K$ under the centre, bounded on each determinant-norm slab $[d_1,d_2]$ with $d_1>0$, and nonvanishing only on a band of adelic heights), and `_hψrep` gives, for every $\sigma'\in\mathbb{R}$ and every $g$, the representation $\psi(g)=\sum_{e}(4\pi)^{-1}\int_{\mathbb{R}}\hat\psi_e(\sigma'+it,g)\,dt$. A matching $\mathrm{em}:\iota_P\to\iota_E$ and shifts $\tau:\iota_P\to\mathbb{R}$ satisfy `_hem`: $\mu_{P,i}=\mu_{\mathrm{em}(i)}\cdot\|\cdot\|^{i\tau_i}$ and $\nu_{P,i}=\nu_{\mathrm{em}(i)}\cdot\|\cdot\|^{-i\tau_i}$, where $\|\cdot\|^{i t}$ is [`NumberField.TateGlobal.normPowChar K t`](def/NumberField_NormPowChar.html#L22). Finally `_hψlev` and `_hψty` require each $\hat\psi_i(s,\cdot)$ to be right invariant under $\Gamma(N)\cap$ the finite-adelic subgroup and to lie in the archimedean cut submodule, and $i_0\in\iota$ is a chosen basis index.
--
--   Conclusion: the integral over the canonical truncation domain, against the adelic Haar measure, of
--   $$\Big(\sum_{i\in\iota_P}\int_{\mathbb{R}}\sum_{j<n_{\mathrm{em}(i)}}\Big(\int_{\mathbf{K}}\hat\psi_i(it,k)\,\overline{\varphi_{\mathrm{em}(i),j}\big((t+\tau_i)i,\;k\big)}\,dk\Big)\,E_{\mathrm{em}(i),j}\big((t+\tau_i)i,\;g\big)\,dt\Big)\cdot\overline{b_{i_0}(g)}$$
--   vanishes; here the inner integral is over the adelic maximal compact subgroup against `maximalCompactHaar K`, and the arguments $it$ and $(t+\tau_i)i$ denote the corresponding purely imaginary complex numbers.
--
--   This is the orthogonality, on the truncation domain, of the unitary-axis Eisenstein wave packet attached to a matched Paley–Wiener datum against each member of the orthonormal basis of the level-$N$, type-cut isotypic cuspidal spaces: the continuous-spectrum share of the statement that the difference between a pseudo-Eisenstein series, its residual projection and the wave packet is orthogonal to all cusp forms. It is used by [`AutomorphicForm.exists_forall_pseudoEisenstein_sub_residualProj_ae_eq_mul_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener`](thm.html#AutomorphicForm.exists_forall_pseudoEisenstein_sub_residualProj_ae_eq_mul_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener), the one-term wave-packet representation of such a difference.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_sum_integral_sum_inner_mul_axis_continuation_mul_conj_cuspBasis_eq_zero_of_matched_paleyWiener.lean

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

theorem AutomorphicForm.setIntegral_sum_integral_sum_inner_mul_axis_continuation_mul_conj_cuspBasis_eq_zero_of_matched_paleyWiener
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
      (_hψty : ∀ i (s : ℂ), ψf i s ∈ archCutSubmodule K tysK)
      (i₀ : ι),
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        (∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
          (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
          EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) * conj (b i₀ g)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by sorry
