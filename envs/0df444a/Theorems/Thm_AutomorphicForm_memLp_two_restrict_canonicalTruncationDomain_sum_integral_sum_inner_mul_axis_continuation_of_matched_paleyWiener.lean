-- Prove2me | Theorems.Thm_AutomorphicForm_memLp_two_restrict_canonicalTruncationDomain_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener
-- name    : AutomorphicForm.memLp_two_restrict_canonicalTruncationDomain_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/d80d148b-88cf-5df3-b044-9a8b8f53b153
-- title:
--   Square-integrability of the axis Eisenstein wave packet
-- statement:
--   Throughout, $K$ is a number field, $\mathbb{A}_K$ its adele ring, and $GL_2(\mathbb{A}_K)$ (written `AdelicGL2 (𝓞 K) K`) carries the Borel structure `glBorel` and the Haar measure $\mu :=$ `adelicGLHaar (Fin 2) (𝓞 K) K`. Fixed are reals $\alpha,\beta$ with $0<\alpha$ (`hα`) and $\alpha<\beta$ (`hαβ`), and $\Phi_0 :=$ [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) denotes the set of matrices selected as truncation domain for the slab $[\alpha,\beta]$ (the last component of a chosen truncation datum, when one exists, and $\emptyset$ otherwise).
--
--   *Siegel covering data.* Reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}$, $d_{1K}<d_{2K}$ and a finite set $T_K\subseteq GL_2(\mathbb{A}_K)$ are given such that `hcovK` holds: the union $\bigcup_{x\in T_K}(\cdot\,x)''\,$`centreCutSiegelSet K cK uK d₁K d₂K` covers $GL_2(\mathbb{A}_K)$ modulo the centre, i.e. for every $g$ there are $\gamma\in GL_2(K)$ and an idele $z$ with $\gamma g\,z\cdot 1$ in that union, $\gamma$ and $z$ being inserted through `globalPoints` and `centralScalar`. Here the centre-cut Siegel set consists of those $g$ whose finite part lies in `finiteIntegralGL2`, and which at every infinite place $w$ satisfy $c_K\le$ `localHeight`, `xWindowSq`$\,\le u_K^2$ and `archDetNorm`$_w\,g\in[d_{1K},d_{2K}]$. A further set $\Phi_K\subseteq GL_2(\mathbb{A}_K)$ occurs as a parameter and is constrained by no hypothesis.
--
--   *Idele measure data.* The idele group $\mathbb{A}_K^\times$ carries a measurable and Borel structure and a Haar measure $\nu_{ZK}$, and $\Omega_K$ is a fundamental domain (`hΩK`) for the range of $K^\times\to\mathbb{A}_K^\times$ with respect to $\nu_{ZK}$.
--
--   *Central character, level, archimedean types.* $S_K$ is a finite set of finite places; $\xi_K$ is a homomorphism from the full subgroup $\top\le\mathbb{A}_K^\times$ to $\mathbb{C}^\times$ whose associated function on ideles is continuous (`hξc`), takes the value $1$ on principal ideles (`hξt`) and has modulus $1$ everywhere (`hξu`); $N$ is an ideal of $\mathcal{O}_K$ such that every $v$ with $v$'s prime ideal dividing $N$ lies in $S_K$ (`hN`); and `tysK : ArchTypeFamily K` prescribes at each infinite place $w$ a finite list of representations of the row-isometry group. The character $\alpha_m$ is the unit-valued real character obtained from `distribHaarChar (AdeleRing (𝓞 K) K)` through `NNReal.toRealHom`, assumed pointwise positive (`hαm`); the adeles carry the Borel structure `adeleBorel`.
--
--   *Carrier data.* Write `pins` for `productionPinsOf K Φ₀ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: the truncation domain $\Phi_0$ together with $Z=\top$, the Haar measure $\mu$ on $GL_2(\mathbb{A}_K)$, the level subgroups $U(M)=$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, the Hecke generators `heckeGen`, and the Haar measure on $\mathbb{A}_K$ conditioned on the box `adelicBox K`.
--
--   *Cusp-form basis (universally quantified).* A type $\iota$, functions $b:\iota\to(GL_2(\mathbb{A}_K)\to\mathbb{C})$ and $\mathrm{cls}:\iota\to$ `HeckeEigensystem K ℂ` are given with: `hb`, each $\mathrm{cls}\,i$ lies in `cuspClasses K pins ξK N SK` (level $N$, vanishing $a_v$ and $b_v$ for $v\in S_K$, non-zero isotypic cusp submodule) and $b\,i$ lies in the intersection of `isotypicCuspSubmodule K pins ξK N SK (cls i)` — the span of the functions that are smooth cuspidal automorphic for `pins` and $\xi_K$, continuous, right $U(N)$-invariant, Hecke eigenfunctions with eigenvalue $a_v$ and central eigenfunctions with eigenvalue $b_v$ for $v\notin S_K$ — with `archCutSubmodule K tysK`, the intersection over infinite places of the sums of the prescribed archimedean type subspaces; `hbn`, $\int_{\Phi_0} b\,i\cdot\overline{b\,i}\,d\mu=1$; `hbo`, $\int_{\Phi_0} b\,i\cdot\overline{b\,j}\,d\mu=0$ for $i\ne j$; `hbs`, for each cusp class $\pi$ the fibre $\{i\mid \mathrm{cls}\,i=\pi\}$ is finite and the complex span of its image under $b$ is the intersection of the $\pi$-isotypic cusp submodule with `archCutSubmodule K tysK`; and `hbc` (completeness): any $\varphi$ that is smooth cuspidal automorphic for `pins` and $\xi_K$, continuous, right invariant under $U(N)$, a member of `archCutSubmodule K tysK`, and orthogonal over $\Phi_0$ to every $b\,i$, vanishes $\mu$-almost everywhere on $\Phi_0$.
--
--   *Continuous-spectrum frame.* A countable type $\iota_E$ and families $\mu,\nu:\iota_E\to\mathrm{Hom}(\mathbb{A}_K^\times,\mathbb{C}^\times)$ are given, with the hypotheses (summarised by name here, each in full force): `_hμ`, `_hν` unitarity in the sense of `IsUnitaryChar`; `_hμic`, `_hνic` triviality on $K^\times$ in the sense of `IsIdeleClassChar`; `_hμc`, `_hνc` continuity; `_hμν` the product relation $\mu_e(z)\nu_e(z)=\xi_K(z)$ for all $z$; `_hdist` separation: distinct $e,e'$ are distinguished by some norm-one idele. Integers $n_E(e)$ and sections $\varphi_{E}(e,j,s,\cdot)$, $j<n_E(e)$, are given with: `_hφE`, each is an induced section for the pair `etaFst (μ e) αm hαm s` $=\mu_e\,\alpha_m^{s+1/2}$ and `etaSnd (ν e) αm hαm s` $=\nu_e\,\alpha_m^{-(s+1/2)}$, i.e. $\varphi(bg)=\eta_1(b_{11})\eta_2(b_{22})\varphi(g)$ for $b$ in the adelic Borel subgroup; `_hφEK` archimedean $K$-finiteness at every infinite place; `_hφEf` smoothness for the finite-part subgroup; `_hφEjc` joint continuity in $(s,g)$; `_hφEhol` holomorphy in $s$ for each $g$; `_hφEKu` the existence, at each infinite place, of a finite-dimensional space containing all right translates along the row-isometry subgroup, uniformly in $s$ and $g$; `_hφEflat` independence of $s$ on the maximal compact subgroup; `_hφElev` right invariance under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`; `_hφEty` membership in `archCutSubmodule K tysK`; `_hφEon` orthonormality over the maximal compact subgroup for `maximalCompactHaar K`; `_hφEspan` that on the unitary axis $s=it$ every continuous, archimedean $K$-finite, level-$N$-invariant induced section of the prescribed types for $(\mu_e,\nu_e)$ lies in the span of the $\varphi_E(e,j,it)$; and `_hpairs`, that every pair $(\mu',\nu')$ of continuous unitary idele class characters with $\mu'\nu'=\xi_K$ carrying a non-zero such section on the axis agrees with some $(\mu_e,\nu_e)$ on the norm-one ideles.
--
--   *Analytic continuations.* Sets $O_E(e,j)\subseteq\mathbb{C}$ and families $E_E(e,j,s,\cdot)$, $N_E(e,j,s,\cdot)$ are given subject to `_hEE`, whose nine clauses require: $O_E(e,j)$ open and preconnected and containing both the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$; analyticity on a neighbourhood of $O_E(e,j)$ of $s\mapsto E_E(e,j,s,g)$ and of $s\mapsto N_E(e,j,s,g)$ for each $g$; continuity of both on $O_E(e,j)\times GL_2(\mathbb{A}_K)$; and, for $\mathrm{Re}\,s>1/2$, the identities $E_E(e,j,s,g)=\varphi_E(e,j,s,g)+\sum_{\xi\in K}\varphi_E\bigl(e,j,s,\,w\,u(\xi)\,g\bigr)$ with $w=$ `adelicWeyl` and $u(\xi)$ the unipotent matrix of the image of $\xi$, and $N_E(e,j,s,g)=$ `weylIntertwiningIntegral` of $\varphi_E(e,j,s,\cdot)$ at $g$ for the additive adelic Haar measure.
--
--   *Paley–Wiener datum.* A finite type $\iota_P$ and characters $\mu_P,\nu_P:\iota_P\to\mathrm{Hom}(\mathbb{A}_K^\times,\mathbb{C}^\times)$ are given with: `_hμ`, `_hν` unitarity; `_hμic`, `_hνic` triviality on $K^\times$; `_hμc`, `_hνc` continuity; `_hμν` the relation $\mu_P(e)(z)\nu_P(e)(z)=\xi_K(z)$ for $z$ in $Z=\top$; a map $r_P:\iota_P\to\iota_P$ with `_hr`: $\mu_P(r_Pe)=\nu_P(e)$ and $\nu_P(r_Pe)=\mu_P(e)$; `_hdist` separation of distinct indices on the norm-one ideles. Sections $\psi_f(e,s,\cdot)$ satisfy `_hψf` (induced section for `etaFst (μP e) αm hαm s` and `etaSnd (νP e) αm hαm s`), `_hψjc` joint continuity, `_hψhol` holomorphy in $s$, `_hψK` archimedean $K$-finiteness, `_hψsm` finite-part smoothness, `_hψKu` uniform finite-dimensionality of right translates at each infinite place, `_hψlev` right $U(N)$-invariance, `_hψty` membership in `archCutSubmodule K tysK`, and `_hψdec` rapid decay: for every $e$, $n\in\mathbb{N}$, $\sigma_0\in\mathbb{R}$ and compact $C$ there is an integrable, bounded $m:\mathbb{R}\to\mathbb{R}$ with $(1+|t|)^n\|\psi_f(e,\sigma'+it,g)\|\le m(t)$ for all $|\sigma'|\le\sigma_0$, all $t$ and all $g\in C$. A function $\psi$ on $GL_2(\mathbb{A}_K)$ satisfies `_hψ`, [`AutomorphicForm.IsSlabProfile`](def/AutomorphicForm_SlabProfile.html#L17) for $Z=\top$ and $\xi_K$ (measurability, left invariance under adelic unipotents and under global Borel elements, central transformation by $\xi_K$, boundedness on each determinant-norm slab $[d_1,d_2]$ with $d_1>0$, and a height band for its support), and `_hψrep`: for every $\sigma'\in\mathbb{R}$ and every $g$, $\psi(g)=\sum_{e\in\iota_P}(4\pi)^{-1}\int_{\mathbb{R}}\psi_f(e,\sigma'+it,g)\,dt$. Finally maps $\mathrm{em}:\iota_P\to\iota_E$ and $\tau:\iota_P\to\mathbb{R}$ satisfy `_hem`: $\mu_P(i)=\mu_{\mathrm{em}(i)}\cdot$ `normPowChar K (τ i)` and $\nu_P(i)=\nu_{\mathrm{em}(i)}\cdot($`normPowChar K (τ i)`$)^{-1}$, where `normPowChar K t` sends an idele $x$ to $\|x\|^{it}$.
--
--   *Conclusion.* With the wave packet $P:GL_2(\mathbb{A}_K)\to\mathbb{C}$ defined by
--   $$P(g)=\sum_{i\in\iota_P}\int_{\mathbb{R}}\sum_{j<n_E(\mathrm{em}(i))}\Bigl(\int_{\mathbf{K}}\psi_f\bigl(i,it,k\bigr)\,\overline{\varphi_E\bigl(\mathrm{em}(i),j,i(t+\tau_i),k\bigr)}\,d\,\mathrm{maximalCompactHaar}\,K\Bigr)\,E_E\bigl(\mathrm{em}(i),j,i(t+\tau_i),g\bigr)\,dt,$$
--   the integral over $k$ being taken over `adelicMaximalCompact K`, the assertion is that $P$ belongs to $L^2$ of the Haar measure $\mu$ restricted to the canonical truncation domain $\Phi_0$: $P$ is almost everywhere strongly measurable for that restricted measure and $\int_{\Phi_0}\|P\|^2\,d\mu<\infty$.
--
--   This is Langlands' square-integrability lemma for Eisenstein wave packets, in the adelic $GL_2$ form used here: the packet formed on the unitary axis from a matched level-$N$ Paley–Wiener datum is $L^2$ on the truncation domain. It is used by [`AutomorphicForm.exists_forall_pseudoEisenstein_sub_residualProj_ae_eq_mul_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener`](thm.html#AutomorphicForm.exists_forall_pseudoEisenstein_sub_residualProj_ae_eq_mul_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener), where membership of $P$ in $L^2(\Phi_0)$ is what allows the completeness clause of the cusp-form basis to be applied to the difference of the pseudo-Eisenstein series, its residual part and the packet.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_memLp_two_restrict_canonicalTruncationDomain_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener.lean

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

theorem AutomorphicForm.memLp_two_restrict_canonicalTruncationDomain_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener
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
    let P : AdelicGL2 (𝓞 K) K → ℂ := fun g =>
        ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
          (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
          EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g
    MemLp P 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by sorry
