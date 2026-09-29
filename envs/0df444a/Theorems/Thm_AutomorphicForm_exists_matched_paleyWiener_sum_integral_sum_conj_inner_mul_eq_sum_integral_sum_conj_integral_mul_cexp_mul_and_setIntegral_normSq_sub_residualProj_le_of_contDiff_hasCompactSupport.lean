-- Prove2me | Theorems.Thm_AutomorphicForm_exists_matched_paleyWiener_sum_integral_sum_conj_inner_mul_eq_sum_integral_sum_conj_integral_mul_cexp_mul_and_setIntegral_normSq_sub_residualProj_le_of_contDiff_hasCompactSupport
-- name    : AutomorphicForm.exists_matched_paleyWiener_sum_integral_sum_conj_inner_mul_eq_sum_integral_sum_conj_integral_mul_cexp_mul_and_setIntegral_normSq_sub_residualProj_le_of_contDiff_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/3696dd2f-5ada-59d9-be5e-e4e8e790f892
-- title:
--   Matched Paley–Wiener data realising prescribed smooth coefficient families
-- statement:
--   The setting is a number field $K$ and two reals $\alpha<\beta$ with $0<\alpha$, together with the canonical truncation domain $\Phi_0=$ [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) (the set component of a fixed choice of truncation datum for the parameters $\alpha,\beta$) and the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` on $\mathrm{GL}_2$ of the adeles. Throughout, the carrier data are packaged as the production pins `productionPinsOf K Φ₀ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, domain $\Phi_0$, central subgroup $Z=\top$ (all ideles), level subgroups $U(M)=$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, Hecke generators `heckeGen (𝓞 K) K v`, and the additive measure `adelicAddHaar` conditioned on the box `adelicBox K`.
--
--   The ambient hypotheses are: an auxiliary set $\Phi_K$ of adelic matrices; reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}<d_{2K}$ and a finite set $T_K\subseteq\mathrm{GL}_2(\mathbb{A}_K)$ such that `hcovK` holds, i.e. the union of the right translates $(\cdot\,x)$ of `centreCutSiegelSet K cK uK d₁K d₂K` over $x\in T_K$ covers modulo the centre — for every $g$ there are $\gamma\in\mathrm{GL}_2(K)$ and an idele $z$ with $\gamma\, g\, z$ (global point times $g$ times central scalar) in that union; the Siegel set in question consists of those $g$ whose finite part is integral, whose local height is $\ge c_K$ and whose $x$-window satisfies $\mathrm{xWindowSq}\le u_K^2$ at every infinite place, and whose archimedean determinant norms lie in $[d_{1K},d_{2K}]$. Further: a Borel measurable structure on the idele group, a Haar measure $\nu_{Z K}$ on it and a set $\Omega_K$ which by `hΩK` is a fundamental domain for the image of $K^\times$ in the ideles; a finite set $S_K$ of finite places; a character $\xi_K$ of the full idele group with values in $\mathbb{C}^\times$ which is continuous (`hξc`), trivial on principal ideles (`hξt`) and unitary (`hξu`); an ideal $N$ of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$ (`hN`); and an archimedean type family $\mathrm{tys}_K$, assigning to each infinite place $w$ finitely many representations of the row-isometry group at $w$, whence the subspace `archCutSubmodule K tysK` $=\bigsqcap_w\bigsqcup_i$ (type subspace of the $i$-th prescribed type at $w$). Finally $\alpha_m$ denotes the homomorphism from the ideles to $\mathbb{R}^\times$ obtained from the Haar module character `distribHaarChar (AdeleRing (𝓞 K) K)` through $\mathbb{R}_{\ge0}\to\mathbb{R}$, and $h\alpha_m$ asserts that all its values are positive.
--
--   The assertion is the existence of a constant $C>0$, chosen before all the spectral data below, such that the following holds for every choice of those data.
--
--   Cuspidal data: a type $\iota$, functions $b_i:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ and Hecke eigensystems $\mathrm{cls}(i)$ over $\mathbb{C}$ subject to `hb` (each $\mathrm{cls}(i)$ is a cusp class for the pins, $\xi_K$, $N$, $S_K$ — level $N$, vanishing Hecke and central data at the places of $S_K$, and non-zero isotypic space — and $b_i$ lies in `isotypicCuspSubmodule` at $\mathrm{cls}(i)$ intersected with `archCutSubmodule K tysK`, the isotypic space being spanned by the continuous smooth cuspidal $\xi_K$-automorphic functions that are right $U(N)$-invariant, Hecke eigenfunctions with eigenvalues $\Phi.a(v)$ outside $S_K$ and central eigenfunctions with eigenvalues $\Phi.b(v)$); `hbn` and `hbo`, stating $\int_{\Phi_0}b_i\overline{b_i}=1$ and $\int_{\Phi_0}b_i\overline{b_j}=0$ for $i\neq j$; `hbs`, stating that each cusp class $\pi$ has $\{i\mid \mathrm{cls}(i)=\pi\}$ finite with $\mathbb{C}$-span of the corresponding $b_i$ equal to the isotypic space at $\pi$ cut by the archimedean types; and `hbc`, completeness: any $\varphi$ which is smooth cuspidal $\xi_K$-automorphic for the pins, continuous, right $U(N)$-invariant and of the prescribed archimedean types, and orthogonal to every $b_i$ over $\Phi_0$, vanishes almost everywhere on $\Phi_0$.
--
--   Continuous-spectrum data: a countable type $\iota_E$ and families of idele characters $\mu_e,\nu_e$, subject to the hypotheses `_hμ`, `_hν` (unitary), `_hμic`, `_hνic` (trivial on $K^\times$), `_hμc`, `_hνc` (continuous), `_hμν` ($\mu_e\nu_e=\xi_K$) and `_hdist` (for $e\neq e'$ some norm-one idele separates the pairs). Then integers $n_E(e)$ and sections $\varphi_{e,j}(s,\cdot)$, $j\in\mathrm{Fin}(n_E(e))$, subject to the group of hypotheses `_hφE`, `_hφEK`, `_hφEf`, `_hφEjc`, `_hφEhol`, `_hφEKu`, `_hφEflat`, `_hφElev`, `_hφEty`, `_hφEon`, `_hφEspan`: each $\varphi_{e,j}(s,\cdot)$ is an induced section for the characters `etaFst (μ e) αm hαm s` $=\mu_e\alpha_m^{s+1/2}$ and `etaSnd (ν e) αm hαm s` $=\nu_e\alpha_m^{-(s+1/2)}$, meaning $\varphi(bg)=\eta_1(b_{00})\eta_2(b_{11})\varphi(g)$ for $b$ in the adelic Borel subgroup; it is archimedean $K$-finite and $K_f$-smooth; jointly continuous in $(s,g)$ and entire in $s$ for fixed $g$; at each infinite place the right translates under the row-isometry subgroup lie in one fixed finite-dimensional space of functions, uniformly in $s$ and $g$; $\varphi_{e,j}(s,k)=\varphi_{e,j}(0,k)$ for $k$ in `adelicMaximalCompact K`; right invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`; of the prescribed archimedean types; orthonormal on the maximal compact with respect to `maximalCompactHaar K`; and, for each real $t$, spanning: every induced section at $s=it$ for $(\mu_e,\nu_e)$ that is continuous, archimedean $K$-finite, level-$N$ invariant and of the given types lies in the $\mathbb{C}$-span of the $\varphi_{e,j}(it,\cdot)$. The hypothesis `_hpairs` requires exhaustiveness: for any unitary continuous idele class characters $\mu',\nu'$ with $\mu'\nu'=\xi_K$, any real $t$ and any non-zero induced section at $s=it$ of the stated level and types, there is $e$ with $\mu_e=\mu'$ and $\nu_e=\nu'$ on the norm-one ideles. Lastly, sets $O_{e,j}\subseteq\mathbb{C}$ and functions $E_{e,j}$, $N_{e,j}$ subject to `_hEE` (nine clauses): $O_{e,j}$ is open, preconnected and contains both the imaginary axis and the half-plane $\{\mathrm{Re}\,s>1/2\}$; $s\mapsto E_{e,j}(s,g)$ and $s\mapsto N_{e,j}(s,g)$ are analytic on a neighbourhood of $O_{e,j}$ for each $g$; both are continuous on $O_{e,j}\times\mathrm{univ}$; for $\mathrm{Re}\,s>1/2$ one has $E_{e,j}(s,g)=\varphi_{e,j}(s,g)+\sum_{\xi\in K}'\varphi_{e,j}(s,\;w\,u(\xi)\,g)$ with $w=$ `adelicWeyl` and $u$ the unipotent, and $N_{e,j}(s,g)=$ `weylIntertwiningIntegral` of $\varphi_{e,j}(s,\cdot)$ at $g$ against the adelic additive Haar measure, i.e. $\int \varphi_{e,j}(s,w^{-1}u(x)g)\,dx$.
--
--   Test data: a finite set $F\subseteq\iota_E$ and functions $h_{e,j}:\mathbb{R}\to\mathbb{C}$ which by `_hh` are smooth ($\mathrm{ContDiff}\ \mathbb{R}\ \infty$) with compact support, and by `_hhF` vanish identically when $e\notin F$.
--
--   For such data the conclusion asserts the existence of: a finite type $\iota_P$; idele characters $\mu_{P,e},\nu_{P,e}$ which are unitary, idele class characters and continuous, satisfy $\mu_{P,e}(z)\nu_{P,e}(z)=\xi_K(z)$ for all $z$ in the central subgroup $\top$, and are separated on the norm-one ideles for distinct indices; a map $r_P:\iota_P\to\iota_P$ exchanging $\mu_P$ and $\nu_P$ ($\mu_{P,r_P(e)}=\nu_{P,e}$ and $\nu_{P,r_P(e)}=\mu_{P,e}$); sections $\psi_{f,e}(s,\cdot)$ which are induced for `etaFst (μP e) αm hαm s` and `etaSnd (νP e) αm hαm s`, jointly continuous, holomorphic in $s$, archimedean $K$-finite, $K_f$-smooth, with uniformly finite-dimensional $K$-types at each infinite place, and which satisfy the vertical-decay hypothesis `_hψdec`: for every $e$, every $n\in\mathbb{N}$, every $\sigma_0$ and every compact $C$ there is an integrable, bounded-above $m:\mathbb{R}\to\mathbb{R}$ with $(1+|t|)^n\|\psi_{f,e}(\sigma'+it,g)\|\le m(t)$ for all $|\sigma'|\le\sigma_0$, all $t$ and all $g\in C$; a function $\psi$ which is a slab profile for $\top$ and $\xi_K$ (measurable, invariant under left multiplication by unipotents and by global Borel elements, transforming by $\xi_K$ under the centre, bounded on each determinant-norm slab $[d_1,d_2]$ with $d_1>0$, and non-zero only where the adelic height lies in a band $[a,b]$ with $a>0$), represented for every $\sigma'$ and $g$ by $\psi(g)=\sum_{e}(4\pi)^{-1}\int_{\mathbb{R}}\psi_{f,e}(\sigma'+it,g)\,dt$; maps $\mathrm{em}:\iota_P\to\iota_E$ and $\tau:\iota_P\to\mathbb{R}$ with $\mu_{P,i}=\mu_{\mathrm{em}(i)}\cdot\|\cdot\|^{i\tau_i}$ and $\nu_{P,i}=\nu_{\mathrm{em}(i)}\cdot\|\cdot\|^{-i\tau_i}$ in terms of [`NumberField.TateGlobal.normPowChar`](def/NumberField_NormPowChar.html#L22); level-$N$ right invariance and membership in the prescribed archimedean types for every $\psi_{f,i}(s,\cdot)$; and finally a function $p_\psi$ satisfying `IsAutomorphicFnAt` for the pins and $\xi_K$ (that is, `LsXiMember` for `adelicGLHaar`, the domain $\Phi_0$, the central subgroup $\top$ and $\xi_K$), lying in the $L^2(\Phi_0)$-closure of the residual span in the sense of `_hpψc` (for each $\varepsilon>0$ there is $r$ in [`AutomorphicForm.residualSpan`](def/AutomorphicForm_ResidualSpan.html#L12), the span of the functions $\chi\circ\det$ for characters $\chi$ with $\chi^2=\xi_K$ on the centre, with $r$ automorphic for the pins and $\mathrm{eLpNorm}(p_\psi-r,2)$ over $\Phi_0$ less than $\varepsilon$), and orthogonal to the residual span in the sense of `_hpψo` ($\int_{\Phi_0}(\theta_\psi(g)-p_\psi(g))\overline{r(g)}=0$ for every automorphic $r$ in the residual span), where $\theta_\psi=$ [`AutomorphicForm.pseudoEisenstein K ψ`](def/AutomorphicForm_SlabProfile.html#L32), $\theta_\psi(g)=\psi(g)+\sum_{\beta\in K}'\psi(w\,u(\beta)\,g)$.
--
--   The two conjuncts of the final conclusion are as follows. First, for every family $\Theta_{e,j}:\mathbb{R}\to\mathbb{C}$ indexed by $e:\iota_E$ and $j\in\mathrm{Fin}(n_E(e))$,
--   $$\sum_{i:\iota_P}\int_{\mathbb{R}}\sum_{j}\overline{\Big(\int_{\mathbf{K}}\psi_{f,i}(it,k)\,\overline{\varphi_{\mathrm{em}(i),j}(i(t+\tau_i),k)}\,d\mathrm{maximalCompactHaar}\Big)}\;\Theta_{\mathrm{em}(i),j}(t+\tau_i)\,dt=\sum_{e\in F}\int_{\mathbb{R}}\sum_{j}\overline{\Big(\int_{\mathbb{R}}h_{e,j}(x)e^{itx}\,dx\Big)}\;\Theta_{e,j}(t)\,dt,$$
--   where $\mathbf{K}=$ `adelicMaximalCompact K` and the inner sum on the left runs over $j\in\mathrm{Fin}(n_E(\mathrm{em}(i)))$; no integrability is asserted separately, the identity being one of Bochner integrals. Second,
--   $$\int_{\Phi_0}\|\theta_\psi(g)-p_\psi(g)\|^2\,d\mathrm{adelicGLHaar}\;\le\;C\sum_{e\in F}\sum_{j}\int_{\mathbb{R}}\Big\|\int_{\mathbb{R}}h_{e,j}(x)e^{itx}\,dx\Big\|^2\,dt.$$
--
--   This is the supply step of the continuous-spectrum analysis: it realises an arbitrary finite family of smooth compactly supported functions $h_{e,j}$ on $\mathbb{R}$ by a matched Paley–Wiener datum $(\psi_{f},\psi,p_\psi)$ of the prescribed level and archimedean types, whose canonical coefficients pair against any test family exactly as the Fourier transforms $\hat h_{e,j}(t)=\int h_{e,j}(x)e^{itx}dx$ do, and whose pseudo-Eisenstein series, after removal of its residual part, has $L^2(\Phi_0)$-norm controlled by $\sum_{e,j}\|\hat h_{e,j}\|_{L^2}^2$ with a constant depending only on the ambient data. It is obtained from the single result [`AutomorphicForm.exists_matched_paleyWiener_injective_and_inner_eq_integral_mul_cexp_and_sum_integral_sum_conj_inner_mul_eq_and_setIntegral_normSq_sub_residualProj_le_of_contDiff_hasCompactSupport`](thm.html#AutomorphicForm.exists_matched_paleyWiener_injective_and_inner_eq_integral_mul_cexp_and_sum_integral_sum_conj_inner_mul_eq_and_setIntegral_normSq_sub_residualProj_le_of_contDiff_hasCompactSupport) by keeping only the matching identity and the norm bound, and feeds the Bessel inequality for the coefficients of $\theta_\Psi$ proved in [`AutomorphicForm.exists_forall_memLp_two_and_summable_and_tsum_integral_sum_normSq_setIntegral_finsum_integral_indicator_mul_conj_axis_continuation_le_mul_setIntegral_normSq`](thm.html#AutomorphicForm.exists_forall_memLp_two_and_summable_and_tsum_integral_sum_normSq_setIntegral_finsum_integral_indicator_mul_conj_axis_continuation_le_mul_setIntegral_normSq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_matched_paleyWiener_sum_integral_sum_conj_inner_mul_eq_sum_integral_sum_conj_integral_mul_cexp_mul_and_setIntegral_normSq_sub_residualProj_le_of_contDiff_hasCompactSupport.lean

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

theorem AutomorphicForm.exists_matched_paleyWiener_sum_integral_sum_conj_inner_mul_eq_sum_integral_sum_conj_integral_mul_cexp_mul_and_setIntegral_normSq_sub_residualProj_le_of_contDiff_hasCompactSupport
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
    ∃ C : ℝ, 0 < C ∧
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
      (F : Finset ιE)
      (h : (e : ιE) → Fin (nE e) → ℝ → ℂ)
      (_hh : ∀ (e : ιE) (j : Fin (nE e)), ContDiff ℝ ∞ (h e j) ∧ HasCompactSupport (h e j))
      (_hhF : ∀ (e : ιE), e ∉ F → ∀ (j : Fin (nE e)), h e j = 0),
    ∃ (ιP : Type) (_instP : Fintype ιP)
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
      (pψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hpψ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK pψ)
      (_hpψc : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (pψ - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hpψo : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            (AutomorphicForm.pseudoEisenstein K ψ g - pψ g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0),
    (∀ (Θ : (e : ιE) → Fin (nE e) → ℝ → ℂ),
      ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
          conj (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) * Θ (em i) j (t + τ i)
        = ∑ e ∈ F, ∫ t : ℝ, ∑ j : Fin (nE e), conj (∫ x : ℝ, h e j x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) * Θ e j t) ∧
    (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ‖AutomorphicForm.pseudoEisenstein K ψ g - pψ g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
        ≤ C * ∑ e ∈ F, ∑ j : Fin (nE e), ∫ t : ℝ, ‖(∫ x : ℝ, h e j x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)))‖ ^ 2) := by sorry
