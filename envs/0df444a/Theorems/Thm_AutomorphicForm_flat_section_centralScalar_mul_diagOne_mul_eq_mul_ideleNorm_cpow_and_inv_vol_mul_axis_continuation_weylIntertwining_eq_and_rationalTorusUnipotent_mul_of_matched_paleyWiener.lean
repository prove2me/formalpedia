-- Prove2me | Theorems.Thm_AutomorphicForm_flat_section_centralScalar_mul_diagOne_mul_eq_mul_ideleNorm_cpow_and_inv_vol_mul_axis_continuation_weylIntertwining_eq_and_rationalTorusUnipotent_mul_of_matched_paleyWiener
-- name    : AutomorphicForm.flat_section_centralScalar_mul_diagOne_mul_eq_mul_ideleNorm_cpow_and_inv_vol_mul_axis_continuation_weylIntertwining_eq_and_rationalTorusUnipotent_mul_of_matched_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/42399e89-7402-5e9d-a033-ccb2cea32fbf
-- title:
--   Iwasawa law for flat sections and continued intertwining amplitudes
-- statement:
--   Fix a number field $K$ and real numbers $\alpha,\beta$ with $0<\alpha<\beta$ (`hα`, `hαβ`).
--
--   **Siegel covering data.** A set $\Phi_K\subseteq\mathrm{GL}_2(\mathbb A_K)$ is taken as a parameter; it occurs in no hypothesis and not in the conclusion. Real numbers $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$ (`hcK`), $0<d_{1K}$ (`hd₁K`), $d_{1K}<d_{2K}$ (`hdK`) and a finite set $T_K\subseteq\mathrm{GL}_2(\mathbb A_K)$ are given such that the union of the right translates $g\mapsto gx$, $x\in T_K$, of the centre-cut Siegel set `centreCutSiegelSet K cK uK d₁K d₂K` covers $\mathrm{GL}_2(\mathbb A_K)$ modulo the centre (`hcovK`): for every $g$ there are $\gamma\in\mathrm{GL}_2(K)$ and an idele $z$ with $\iota(\gamma)\,g\,c(z)$ in that union, where $\iota$ is the map `globalPoints` on rational points and $c(z)$ is the scalar matrix `centralScalar` of $z$. The centre-cut Siegel set consists of those $g$ whose finite part is integral and which at every infinite place $w$ satisfy $c_K\le\,$`localHeight`, `xWindowSq`$\,\le u_K^2$ and `archDetNorm`$\,\in[d_{1K},d_{2K}]$.
--
--   **Central data on the idele group.** The idele group $\mathbb A_K^\times$ carries a measurable structure and is a Borel space; $\nu_{ZK}$ is a Haar measure on it and $\Omega_K$ a fundamental domain for the subgroup of principal ideles, i.e. for the range of $K^\times\to\mathbb A_K^\times$ (`hΩK`). A finite set $S_K$ of finite places of $K$ is given, together with a homomorphism $\xi_K$ from the top subgroup of $\mathbb A_K^\times$ to $\mathbb C^\times$ which is continuous (`hξc`), trivial on principal ideles (`hξt`) and of absolute value $1$ at every idele (`hξu`). An ideal $N\subseteq\mathcal O_K$ is given with every finite place dividing $N$ lying in $S_K$ (`hN`), and an archimedean type family $\mathrm{tys}_K$ (at each infinite place $w$ a finite list of representations of the row-isometry group of $K_w$, cutting out `archCutSubmodule K tysK`).
--
--   Write $\alpha_m$ for the idelic module character, the unit-group homomorphism $\mathbb A_K^\times\to\mathbb R^\times$ obtained from `distribHaarChar (AdeleRing (𝓞 K) K)` by coercing $\mathbb R_{\ge0}$ into $\mathbb R$, and assume $\alpha_m$ is everywhere positive (`hαm`). Throughout, `pins` abbreviates `productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: the Borel $\sigma$-algebra and Haar measure on $\mathrm{GL}_2(\mathbb A_K)$, the canonical truncation domain attached to $(\alpha,\beta)$ as test domain, the top subgroup of $\mathbb A_K^\times$ as central subgroup, the principal level subgroups intersected with the finite part, the Hecke generators `heckeGen`, and on $\mathbb A_K$ the Borel $\sigma$-algebra with the additive Haar measure conditioned on the adelic box.
--
--   **Cuspidal orthonormal family.** A type $\iota$, functions $b:\iota\to(\mathrm{GL}_2(\mathbb A_K)\to\mathbb C)$ and $\mathrm{cls}:\iota\to$ `HeckeEigensystem K ℂ` are given with: `hb`, each $\mathrm{cls}\,i$ is a cusp class for `pins`, $\xi_K$, $N$, $S_K$ (level $N$, vanishing eigenvalues at the places of $S_K$, non-vanishing isotypic space) and $b\,i$ lies in the intersection of the isotypic cuspidal submodule of $\mathrm{cls}\,i$ with the archimedean type submodule; `hbn` and `hbo`, the $b\,i$ are orthonormal for the pairing $\int_{D}\varphi\,\overline{\psi}$ over the canonical truncation domain against adelic Haar measure; `hbs`, for each cusp class $\pi$ the fibre $\{i\mid \mathrm{cls}\,i=\pi\}$ is finite and the $\mathbb C$-span of its image under $b$ is exactly the $\pi$-isotypic cuspidal submodule intersected with the archimedean type submodule; `hbc`, completeness — any $\varphi$ that is a smooth cuspidal automorphic function for `pins` and $\xi_K$, continuous, invariant under right translation by the level subgroup `pins.U N`, of the prescribed archimedean type, and orthogonal to every $b\,i$ over the truncation domain, vanishes almost everywhere on that domain.
--
--   **Continuous-spectrum family.** A countable type $\iota_E$ and families $\mu,\nu:\iota_E\to\mathrm{Hom}(\mathbb A_K^\times,\mathbb C^\times)$ are given, each $\mu_e,\nu_e$ unitary, an idele class character, and continuous, with $\mu_e\nu_e=\xi_K$ pointwise, and distinct indices separated already on the norm-one ideles. Integers $n_E(e)$ and functions $\varphi_{e,j}:\mathbb C\to(\mathrm{GL}_2(\mathbb A_K)\to\mathbb C)$ are given subject to: each $\varphi_{e,j}(s)$ is an induced section for the pair $\big(\mu_e|\cdot|^{s+1/2},\nu_e|\cdot|^{-(s+1/2)}\big)$ in the sense of `IsInducedSection` (with $|\cdot|$ the character $\alpha_m$ raised to a complex power, the transformation being through the diagonal entries of an element of the adelic Borel subgroup); archimedean $K$-finiteness; $K_f$-smoothness; joint continuity in $(s,g)$; holomorphy in $s$ for each $g$; uniform archimedean $K$-type (a finite-dimensional space of functions on the row-isometry subgroup at each infinite place containing all right-translate functions); flatness, $\varphi_{e,j}(s)=\varphi_{e,j}(0)$ on the adelic maximal compact subgroup; invariance under right translation by `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`; membership in the archimedean type submodule; orthonormality of the $\varphi_{e,j}(0)$ over the maximal compact subgroup against `maximalCompactHaar K`; spanning (`_hφEspan`), every section on the imaginary axis with the listed regularity, level and type properties lies in the span of the $\varphi_{e,j}(it)$; and exhaustiveness (`_hpairs`), every pair of continuous unitary idele class characters with product $\xi_K$ admitting a non-zero such section on the axis agrees with some $(\mu_e,\nu_e)$ on the norm-one ideles. Sets $O_{e,j}\subseteq\mathbb C$ and functions $E_{e,j},N_{e,j}$ are given with (`_hEE`) $O_{e,j}$ open and preconnected, containing the line $\{\operatorname{Re}s=0\}$ and the half-plane $\{\operatorname{Re}s>1/2\}$, with $s\mapsto E_{e,j}(s)(g)$ and $s\mapsto N_{e,j}(s)(g)$ analytic on a neighbourhood of $O_{e,j}$ for each $g$, both jointly continuous on $O_{e,j}\times\mathrm{GL}_2(\mathbb A_K)$, and for $\operatorname{Re}s>1/2$: $E_{e,j}(s)(g)=\varphi_{e,j}(s)(g)+\sum_{\xi\in K}\varphi_{e,j}(s)(w\,n(\xi)\,g)$ with $w$ the adelic Weyl element and $n(\xi)$ the rational unipotent matrix, and $N_{e,j}(s)(g)$ equal to the Weyl intertwining integral $\int_{\mathbb A_K}\varphi_{e,j}(s)(w^{-1}n(x)g)\,dx$ against additive adelic Haar measure.
--
--   **Paley–Wiener datum.** A finite type $\iota_P$ and characters $\mu_P,\nu_P:\iota_P\to\mathrm{Hom}(\mathbb A_K^\times,\mathbb C^\times)$ are given, unitary, idele class characters, continuous, with $\mu_P(e)\nu_P(e)=\xi_K$ on the central subgroup of `pins`, together with an index map $r_P$ interchanging $\mu_P$ and $\nu_P$, and separation of distinct indices on the norm-one ideles. Functions $\psi_e:\mathbb C\to(\mathrm{GL}_2(\mathbb A_K)\to\mathbb C)$ are given which are induced sections for $\big(\mu_P(e)|\cdot|^{s+1/2},\nu_P(e)|\cdot|^{-(s+1/2)}\big)$, jointly continuous, holomorphic in $s$, archimedean $K$-finite, $K_f$-smooth, of uniform archimedean $K$-type, level-$N$ invariant (`_hψlev`), of the prescribed archimedean type (`_hψty`), and of rapid decay in vertical strips (`_hψdec`): for each $e$, each $n\in\mathbb N$, each $\sigma_0$ and each compact $C$ there is an integrable, bounded-above $m:\mathbb R\to\mathbb R$ with $(1+|t|)^n\,\|\psi_e(\sigma'+it)(g)\|\le m(t)$ for $|\sigma'|\le\sigma_0$, all $t$ and all $g\in C$. Finally a function $\psi$ is given which is a slab profile for the central subgroup and $\xi_K$ (measurable, invariant under left multiplication by adelic unipotents and by rational Borel elements, transforming by $\xi_K$ under the centre, bounded on determinant-norm slabs, supported in a height band) and which is represented, for every $\sigma'$ and every $g$, by the wave packet $\psi(g)=\sum_{e}(4\pi)^{-1}\int_{\mathbb R}\psi_e(\sigma'+it)(g)\,dt$ (`_hψrep`).
--
--   **Matching data.** Maps $\mathrm{em}:\iota_P\to\iota_E$ and $\tau:\iota_P\to\mathbb R$ are given with $\mu_P(i)=\mu_{\mathrm{em}(i)}\cdot\|\cdot\|^{i\tau_i}$ and $\nu_P(i)=\nu_{\mathrm{em}(i)}\cdot\|\cdot\|^{-i\tau_i}$, where $\|\cdot\|^{i\tau}$ denotes [`NumberField.TateGlobal.normPowChar K τ`](def/NumberField_NormPowChar.html#L22), the character $x\mapsto \|x\|^{i\tau}$ in the idelic norm.
--
--   **Conclusion.** Set $v=$ `((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal`, the volume of the adelic box, and for $i\in\iota_P$ and $t\in\mathbb R$ put $s_i=(t+\tau_i)\,\mathrm i$. Then for every $i\in\iota_P$, every $j\in\mathrm{Fin}(n_E(\mathrm{em}(i)))$, every $t\in\mathbb R$, all ideles $z,y$ and every $k$ in the adelic maximal compact subgroup, all three of the following hold.
--
--   First, with $c(z)$ the scalar matrix of $z$ and $a(y)=$ `diagOne y` $=\mathrm{diag}(y,1)$,
--   $$\varphi_{\mathrm{em}(i),j}(s_i)\big(c(z)a(y)k\big)=\mu_{\mathrm{em}(i)}(z)\,\nu_{\mathrm{em}(i)}(z)\,\mu_{\mathrm{em}(i)}(y)\,\|y\|^{\,s_i+1/2}\,\varphi_{\mathrm{em}(i),j}(0)(k),$$
--   where $\|y\|=$ [`NumberField.TateGlobal.ideleNorm K y`](def/NumberField_TateGlobalZeta.html#L19), coerced into $\mathbb C$, and the exponent is the complex number $s_i+1/2$.
--
--   Second, for the normalised continued intertwining amplitude $v^{-1}N_{\mathrm{em}(i),j}(s_i)$,
--   $$v^{-1}N_{\mathrm{em}(i),j}(s_i)\big(c(z)a(y)k\big)=\mu_{\mathrm{em}(i)}(z)\,\nu_{\mathrm{em}(i)}(z)\,\nu_{\mathrm{em}(i)}(y)\,\|y\|^{-s_i+1/2}\cdot\Big(v^{-1}N_{\mathrm{em}(i),j}(s_i)(k)\Big).$$
--
--   Third, for every $x$ in the subgroup `rationalTorusUnipotent K`, the join of the rational centre, the rational diagonal-one torus and the full adelic unipotent subgroup, and every $g\in\mathrm{GL}_2(\mathbb A_K)$,
--   $$\varphi_{\mathrm{em}(i),j}(s_i)(xg)=\varphi_{\mathrm{em}(i),j}(s_i)(g),\qquad N_{\mathrm{em}(i),j}(s_i)(xg)=N_{\mathrm{em}(i),j}(s_i)(g).$$
--
--   This is the pointwise Iwasawa evaluation, at a fixed point $s_i=(t+\tau_i)\mathrm i$ of the unitary axis, of the two constant-term amplitudes attached to a matched Paley–Wiener wave packet of one-term Eisenstein series: the incoming flat section and the normalised analytic continuation of the Weyl intertwining integral, together with their invariance under the rational torus and the adelic unipotent radical. It is the transported, matched-index form of the single-pair statement `AutomorphicForm.orthonormal_and_isInducedSection_inv_vol_mu...weylIntertwiningIntegral_of_flat_orthonormal_family`, and it is used by [`AutomorphicForm.exists_forall_memLp_two_indicator_highSet_sum_integral_sum_inner_mul_add_inv_vol_mul_axis_continuation_weylIntertwining_of_matched_paleyWiener`](thm.html#AutomorphicForm.exists_forall_memLp_two_indicator_highSet_sum_integral_sum_inner_mul_add_inv_vol_mul_axis_continuation_weylIntertwining_of_matched_paleyWiener) in the analysis of the continuous part of the spectral decomposition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_flat_section_centralScalar_mul_diagOne_mul_eq_mul_ideleNorm_cpow_and_inv_vol_mul_axis_continuation_weylIntertwining_eq_and_rationalTorusUnipotent_mul_of_matched_paleyWiener.lean

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
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.flat_section_centralScalar_mul_diagOne_mul_eq_mul_ideleNorm_cpow_and_inv_vol_mul_axis_continuation_weylIntertwining_eq_and_rationalTorusUnipotent_mul_of_matched_paleyWiener
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
    ∀ (i : ιP) (j : Fin (nE (em i))) (t : ℝ) (z y : (AdeleRing (𝓞 K) K)ˣ) (k : adelicMaximalCompact K),
      φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K)) =
          ((μ (em i) z : ℂˣ) : ℂ) * ((ν (em i) z : ℂˣ) : ℂ) * ((μ (em i) y : ℂˣ) : ℂ) *
            ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) ^ (((((t + τ i : ℝ) : ℂ)) * Complex.I) + 1 / 2) *
            φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K) ∧
      ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K)) =
          ((μ (em i) z : ℂˣ) : ℂ) * ((ν (em i) z : ℂˣ) : ℂ) * ((ν (em i) y : ℂˣ) : ℂ) *
            ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) ^ (-((((t + τ i : ℝ) : ℂ)) * Complex.I) + 1 / 2) *
            (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∧
      (∀ x ∈ rationalTorusUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K,
        φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (x * g) = φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g ∧
          NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (x * g) = NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) := by sorry
