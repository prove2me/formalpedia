-- Prove2me | Theorems.Thm_AutomorphicForm_inner_weylIntertwining_eq_sum_inner_mul_conj_inner_of_matched_paleyWiener
-- name    : AutomorphicForm.inner_weylIntertwining_eq_sum_inner_mul_conj_inner_of_matched_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/7563afb7-2c65-5463-b461-9caeb2928de5
-- title:
--   Parseval expansion of the intertwined Weyl coefficient over K
-- statement:
--   Throughout, $\mathbb{A}$ denotes the adele ring `AdeleRing (𝓞 K) K` of a number field $K$, $G=\mathrm{GL}_2(\mathbb{A})$ denotes `AdelicGL2 (𝓞 K) K`, $\mathbf{K}=$ `adelicMaximalCompact K` is the subgroup of those $g\in G$ whose finite part lies in `finiteIntegralGL2` and whose component at every infinite place is a row isometry, and $\kappa=$ `maximalCompactHaar K` is the Haar measure on $\mathbf{K}$. The adele ring carries the Borel structure `adeleBorel`.
--
--   **Geometric and covering data.** Reals $\alpha,\beta$ with $0<\alpha$ and $\alpha<\beta$; a set $\Phi_K\subseteq G$, on which no condition is imposed; reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}<d_{2K}$, and a finite set $T_K\subseteq G$, subject to `hcovK`: the union $\bigcup_{x\in T_K}\,(\,\cdot\,x)\big[\mathrm{centreCutSiegelSet}\ K\ c_K\ u_K\ d_{1K}\ d_{2K}\big]$ covers $G$ modulo the centre, that is, for every $g\in G$ there are $\gamma\in\mathrm{GL}_2(K)$ and an idele $z$ with $\mathrm{globalPoints}(\gamma)\,g\,\mathrm{centralScalar}(z)$ in that union. The centre-cut Siegel set consists of the $g$ with integral finite part, with `localHeight` at least $c_K$ and `xWindowSq` at most $u_K^2$ at every infinite place, and with `archDetNorm` in $[d_{1K},d_{2K}]$ at every infinite place.
--
--   **Idelic data.** A Haar measure $\nu_{Z K}$ on $\mathbb{A}^{\times}$ (for a Borel measurable structure on $\mathbb{A}^{\times}$) and a set $\Omega_K$ which is a fundamental domain, in the sense of `IsFundamentalDomain`, for the subgroup of principal ideles (the range of $K^{\times}\to\mathbb{A}^{\times}$) with respect to $\nu_{ZK}$. A finite set $S_K$ of finite places of $K$. A character $\xi_K$ of the full idele group, presented as a homomorphism $(\top:\text{Subgroup }\mathbb{A}^{\times})\to\mathbb{C}^{\times}$, with `hξc` continuity of $z\mapsto\xi_K(z)$, `hξt` triviality on the principal ideles, and `hξu` unitarity $\lVert\xi_K(z)\rVert=1$ for all $z$. An ideal $N\subseteq\mathcal{O}_K$ with `hN`: every finite place dividing $N$ lies in $S_K$. An archimedean type family $\mathrm{tys}_K$, i.e. for each infinite place $w$ a number $\mathrm{card}(w)$ of representations of the row-isometry subgroup of $K_w$; `archCutSubmodule K tysK` is the intersection over all infinite places $w$ of the sum over $i<\mathrm{card}(w)$ of the corresponding type submodules of $G\to\mathbb{C}$.
--
--   **Modulus character.** $\alpha_m$ is the distributive Haar character of $\mathbb{A}$, pushed along $\mathbb{R}_{\ge0}\to\mathbb{R}$ and regarded as a homomorphism $\mathbb{A}^{\times}\to\mathbb{R}^{\times}$; the hypothesis `hαm` asserts that all its values are positive.
--
--   **The carrier pins.** All automorphic notions below refer to the record $\mathrm{pins}=$ `productionPinsOf K (canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: the σ-algebra `glBorel` and the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` on $G$; the domain $D=$ `canonicalTruncationDomain K α β`, the set extracted by choice from a truncation datum for $(\alpha,\beta)$ when one exists and $\emptyset$ otherwise; central subgroup $Z=\top$; level subgroups $U(M)=$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`; Hecke generators $\mathrm{gen}(v)=$ `heckeGen (𝓞 K) K v`; and on $\mathbb{A}$ the Borel structure with `adelicAddHaar` conditioned on `adelicBox K`.
--
--   **Cuspidal orthonormal frame.** A type $\iota$, functions $b_i:G\to\mathbb{C}$ and Hecke eigensystems $\mathrm{cls}_i\in$ `HeckeEigensystem K ℂ`, subject to: `hb`, each $\mathrm{cls}_i$ lies in `cuspClasses` for $(\mathrm{pins},\xi_K,N,S_K)$ (level $N$, both eigenvalue families vanishing on $S_K$, and nonzero isotypic cusp submodule) and $b_i$ lies in `isotypicCuspSubmodule` of $\mathrm{cls}_i$ intersected with `archCutSubmodule K tysK`, where the isotypic submodule is spanned by the functions which are smooth cuspidal automorphic for $(\mathrm{pins},\xi_K)$, continuous, right $U(N)$-invariant, Hecke eigenfunctions with eigenvalue $\mathrm{cls}_i.a(v)$ and central eigenvalue $\mathrm{cls}_i.b(v)$ at the places $v\notin S_K$; `hbn` and `hbo`, orthonormality $\int_D b_i\overline{b_j}=\delta_{ij}$ against `adelicGLHaar`; `hbs`, for every cusp class $\pi$ the fibre $\{i\mid \mathrm{cls}_i=\pi\}$ is finite and the $\mathbb{C}$-span of $b$ over it equals the isotypic submodule of $\pi$ intersected with `archCutSubmodule K tysK`; and `hbc`, completeness: any $\varphi$ which is smooth cuspidal automorphic for $(\mathrm{pins},\xi_K)$, continuous, right $U(N)$-invariant, of the prescribed archimedean type and orthogonal over $D$ to every $b_i$ vanishes almost everywhere on $D$.
--
--   **Continuous-spectrum frame.** A countable type $\iota_E$ and characters $\mu_e,\nu_e$ of $\mathbb{A}^{\times}$, assumed unitary, trivial on principal ideles, continuous, with $\mu_e\nu_e=\xi_K$, and separated: for $e\ne e'$ some norm-one idele (element of the kernel of the distributive Haar character) at which $\mu$ or $\nu$ differ. Numbers $n_E(e)$ and flat sections $\varphi_{e,j}(s):G\to\mathbb{C}$ for $j<n_E(e)$, subject to the clauses `_hφE`, `_hφEK`, `_hφEf`, `_hφEjc`, `_hφEhol`, `_hφEKu`, `_hφEflat`, `_hφElev`, `_hφEty`, `_hφEon`, `_hφEspan`: each $\varphi_{e,j}(s)$ is an induced section for the pair $\mathrm{etaFst}(\mu_e)=\mu_e\cdot\alpha_m^{\,s+1/2}$, $\mathrm{etaSnd}(\nu_e)=\nu_e\cdot\alpha_m^{-(s+1/2)}$, i.e. $\varphi(bg)=\eta_1(b_{00})\eta_2(b_{11})\varphi(g)$ for all $b$ in the adelic Borel subgroup (lower-left entry zero); arch $K$-finite at every infinite place; smooth for the finite-adelic subgroup; jointly continuous in $(s,g)$; holomorphic in $s$ for each $g$; at each infinite place the right translates by the archimedean row-isometry subgroup lie in one finite-dimensional space, uniformly in $s$ and $g$; flat, in that $\varphi_{e,j}(s)$ and $\varphi_{e,j}(0)$ agree on $\mathbf{K}$; right invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`; lying in `archCutSubmodule K tysK`; orthonormal on $\mathbf{K}$ at $s=0$ with respect to $\kappa$; and spanning, in that for each real $t$ every $\varphi_0$ which is an induced section for the parameters at $s=it$, continuous, arch $K$-finite, level-$N$ invariant and of the prescribed archimedean type lies in the span of $\{\varphi_{e,j}(it)\}_{j}$. The clause `_hpairs` requires in addition that for every pair $(\mu',\nu')$ of unitary continuous characters trivial on principal ideles with $\mu'\nu'=\xi_K$ admitting, for some real $t$, a nonzero $\varphi_0$ with those same section, continuity, $K$-finiteness, level and type properties at $s=it$, there is $e$ with $\mu_e=\mu'$ and $\nu_e=\nu'$ on the norm-one ideles.
--
--   **Eisenstein series and intertwining continuation.** Sets $O_{e,j}\subseteq\mathbb{C}$ and functions $E_{e,j},N_{e,j}:\mathbb{C}\to G\to\mathbb{C}$ subject to `_hEE` (eight clauses): $O_{e,j}$ is open and preconnected and contains both the imaginary axis $\{\operatorname{Re}s=0\}$ and the half-plane $\{\operatorname{Re}s>1/2\}$; for each $g$ both $s\mapsto E_{e,j}(s)(g)$ and $s\mapsto N_{e,j}(s)(g)$ are analytic on a neighbourhood of $O_{e,j}$; both are continuous on $O_{e,j}\times G$; for $\operatorname{Re}s>1/2$ one has $E_{e,j}(s)(g)=\varphi_{e,j}(s)(g)+\sum'_{\xi\in K}\varphi_{e,j}(s)\big(w\,u(\xi)\,g\big)$, with $w=$ `adelicWeyl` the image of the antidiagonal matrix and $u(x)=$ `unipotentGL2 x`; and for $\operatorname{Re}s>1/2$ one has $N_{e,j}(s)(g)=\int_{\mathbb{A}}\varphi_{e,j}(s)\big(w^{-1}u(x)g\big)\,d(\mathrm{adelicAddHaar})(x)$.
--
--   **Paley–Wiener datum and matching.** A finite type $\iota_P$, characters $\mu_{P,e},\nu_{P,e}$ of $\mathbb{A}^{\times}$, unitary, trivial on principal ideles and continuous, with $\mu_{P,e}(z)\nu_{P,e}(z)=\xi_K(z)$ for $z$ in $\mathrm{pins}.Z=\top$; a map $r_P:\iota_P\to\iota_P$ with $\mu_{P,r_P e}=\nu_{P,e}$ and $\nu_{P,r_P e}=\mu_{P,e}$; and separation of distinct indices on the norm-one ideles. Sections $\psi_{e}(s):G\to\mathbb{C}$ which are induced sections for $\big(\mathrm{etaFst}(\mu_{P,e})(s),\mathrm{etaSnd}(\nu_{P,e})(s)\big)$, jointly continuous in $(s,g)$, holomorphic in $s$, arch $K$-finite, smooth for the finite-adelic subgroup, uniformly $K$-finite at each infinite place, and satisfying the vertical-strip decay `_hψdec`: for each $e$, each $n\in\mathbb{N}$, each $\sigma_0$ and each compact $C\subseteq G$ there is an integrable, bounded $m:\mathbb{R}\to\mathbb{R}$ with $(1+|t|)^n\lVert\psi_e(\sigma'+it)(g)\rVert\le m(t)$ for all $|\sigma'|\le\sigma_0$, all $t$ and all $g\in C$. A function $\psi:G\to\mathbb{C}$ which is a slab profile for $(\top,\xi_K)$ — measurable, invariant under left multiplication by unipotents and by global Borel elements, transforming by $\xi_K$ under the centre, bounded on every slab of determinant idele norm in $[d_1,d_2]$ with $d_1>0$, and nonzero only where the adelic height lies in a fixed band — together with `_hψrep`: for every $\sigma'\in\mathbb{R}$ and every $g$, $\psi(g)=\sum_{e}(4\pi)^{-1}\int_{\mathbb{R}}\psi_e(\sigma'+it)(g)\,dt$. Finally maps $\mathrm{em}:\iota_P\to\iota_E$ and $\tau:\iota_P\to\mathbb{R}$ with `_hem`: $\mu_{P,i}=\mu_{\mathrm{em}(i)}\cdot\lVert\cdot\rVert^{\,i\tau_i}$ and $\nu_{P,i}=\nu_{\mathrm{em}(i)}\cdot\lVert\cdot\rVert^{-i\tau_i}$ (the twists being [`NumberField.TateGlobal.normPowChar K (τ i)`](def/NumberField_NormPowChar.html#L22) and its inverse), and the clauses `_hψlev` (right invariance of every $\psi_i(s)$ under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`) and `_hψty` (every $\psi_i(s)$ lies in `archCutSubmodule K tysK`).
--
--   **Conclusion.** Write $v$ for `((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal`, viewed in $\mathbb{C}$. Then for every $i\in\iota_P$, every $j<n_E(\mathrm{em}(i))$ and every $t\in\mathbb{R}$,
--   $$\int_{\mathbf{K}}\psi_{r_P i}(-it)(k)\,\overline{v^{-1}N_{\mathrm{em}(i),j}\big(i(t+\tau_i)\big)(k)}\,d\kappa(k)=\sum_{j'<n_E(\mathrm{em}(r_Pi))}A_{j'}\cdot\overline{B_{j'}},$$
--   where
--   $$A_{j'}=\int_{\mathbf{K}}\psi_{r_Pi}(-it)(k)\,\overline{\varphi_{\mathrm{em}(r_Pi),j'}\big(i(-t+\tau_{r_Pi})\big)(k)}\,d\kappa(k),$$
--   $$B_{j'}=\int_{\mathbf{K}}v^{-1}N_{\mathrm{em}(i),j}\big(i(t+\tau_i)\big)(k)\,\overline{\varphi_{\mathrm{em}(r_Pi),j'}\big(i(-t+\tau_{r_Pi})\big)(k)}\,d\kappa(k),$$
--   all integrals being taken over $\mathbf{K}$ against $\kappa$, with $k$ regarded as an element of $G$, and the complex arguments being $-t\,i$, $(t+\tau_i)\,i$ and $(-t+\tau_{r_Pi})\,i$ respectively.
--
--   This is the finite Parseval identity on the adelic maximal compact subgroup for the continuous part of the spectral expansion: the coefficient pairing a matched Paley–Wiener section against the normalised Weyl intertwining continuation $v^{-1}N$ is expanded in the flat orthonormal family attached to the partner index $r_P i$. It is used in [`AutomorphicForm.exists_matched_paleyWiener_tsum_integral_sum_normSq_sub_setIntegral_axis_continuation_le_of_symmetric`](thm.html#AutomorphicForm.exists_matched_paleyWiener_tsum_integral_sum_normSq_sub_setIntegral_axis_continuation_le_of_symmetric), where the resulting coefficients feed the comparison of the truncated Eisenstein contribution with its axis continuation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_inner_weylIntertwining_eq_sum_inner_mul_conj_inner_of_matched_paleyWiener.lean

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

theorem AutomorphicForm.inner_weylIntertwining_eq_sum_inner_mul_conj_inner_of_matched_paleyWiener
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
    ∀ (i : ιP) (j : Fin (nE (em i))) (t : ℝ),
      (∫ k, ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
          conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) =
      ∑ j' : Fin (nE (em (rP i))),
        (∫ k, ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
            conj (φE (em (rP i)) j' ((((-t + τ (rP i) : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
        conj (∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
            conj (φE (em (rP i)) j' ((((-t + τ (rP i) : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) := by sorry
