-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_axis_continuation_mul_conj_cuspBasis_eq_zero_of_re_gt_half
-- name    : AutomorphicForm.setIntegral_axis_continuation_mul_conj_cuspBasis_eq_zero_of_re_gt_half
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/e4f28a4f-b0ad-5c99-ba3e-d8828ed8bbd5
-- title:
--   Eisenstein continuation orthogonal to cusp basis for Re s>1/2
-- statement:
--   Throughout, $K$ is a number field, $\mathbb{A}_K$ its adele ring, and $\mathrm{GL}_2(\mathbb{A}_K)$ (the type `AdelicGL2 (𝓞 K) K`) carries its Borel $\sigma$-algebra `glBorel` and the Haar measure $\mu_{\mathrm{GL}} =$ `adelicGLHaar (Fin 2) (𝓞 K) K`; $\mathbb{A}_K$ itself carries `adeleBorel` and the additive Haar measure `adelicAddHaar`.
--
--   **Slab and covering data.** Real numbers $\alpha<\beta$ with $0<\alpha$ are fixed, together with real numbers $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}<d_{2K}$ and a finite set $T_K\subseteq \mathrm{GL}_2(\mathbb{A}_K)$; the hypothesis `hcovK` says that the union $\bigcup_{x\in T_K}(\cdot\,x)\,[\,$`centreCutSiegelSet K cK uK d₁K d₂K`$\,]$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo rational points and the centre: for every $g$ there are $\gamma\in\mathrm{GL}_2(K)$ and an idele unit $z$ with $\gamma\, g\, z$ (the image of $\gamma$ under `globalPoints` times $g$ times the central scalar of $z$) in that union. Here `centreCutSiegelSet K cK uK d₁K d₂K` is the set of $g$ whose finite part lies in $\mathrm{GL}_2(\widehat{\mathcal O}_K)$ and whose archimedean component at each infinite place $w$ has `localHeight` at least $c_K$, window quantity `xWindowSq` at most $u_K^2$, and `archDetNorm` in $[d_{1K},d_{2K}]$. A set $\Phi_K\subseteq \mathrm{GL}_2(\mathbb{A}_K)$ is a further parameter on which no hypothesis is imposed and which does not occur in the conclusion.
--
--   **Central data.** The group $\mathbb{A}_K^\times$ is equipped with a measurable structure which is the Borel one, a Haar measure $\nu_{Z_K}$, and a set $\Omega_K$ which by `hΩK` is a fundamental domain for the image of $K^\times$ in $\mathbb{A}_K^\times$ with respect to $\nu_{Z_K}$.
--
--   **Character, level and type data.** $S_K$ is a finite set of finite places of $K$, and $\xi_K$ is a homomorphism from the top subgroup of $\mathbb{A}_K^\times$ to $\mathbb{C}^\times$, subject to: `hξc` continuity of $z\mapsto\xi_K(z)$, `hξt` triviality of $\xi_K$ on the image of $K^\times$, and `hξu` the unitarity $|\xi_K(z)|=1$ for all $z$. Further, $N$ is an ideal of $\mathcal O_K$ with `hN`: every finite place $v$ with $v\mid N$ belongs to $S_K$, and $\mathrm{tys}_K$ is an `ArchTypeFamily K`, i.e. for each infinite place $w$ a finite list of representations of the row-isometry group of $K_w$; `archCutSubmodule K tysK` is the intersection over $w$ of the sums of the corresponding type submodules.
--
--   **The modulus character.** The statement abbreviates by $\alpha_m$ the homomorphism $\mathbb{A}_K^\times\to\mathbb{R}^\times$ obtained from `distribHaarChar (AdeleRing (𝓞 K) K)` by composing with $\mathbb{R}_{\ge0}\to\mathbb{R}$ and passing to units, and assumes `hαm`: $\alpha_m(x)>0$ for all $x$.
--
--   **The carrier record.** Write $\mathrm{pins}$ for `productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: the `CarrierPins K` whose measurable space is `glBorel` and whose measure is $\mu_{\mathrm{GL}}$, whose domain $D$ is the canonical truncation domain $D_{\alpha,\beta}=$ `canonicalTruncationDomain K α β` (the set component of a chosen truncation datum for $(\alpha,\beta)$, empty if none exists), whose central subgroup is all of $\mathbb{A}_K^\times$, whose level subgroup at an ideal $M$ is $\mathrm{principalLevel}(M)\cap\ker(\text{archimedean projection})$, whose Hecke generator at $v$ is `heckeGen (𝓞 K) K v`, and whose additive measure is `adelicAddHaar` conditioned on `adelicBox K`. Since the central subgroup is the top subgroup, $\xi_K$ is a character of $\mathrm{pins}.Z$. Recall that `isotypicCuspSubmodule K pins ξK N SK Φ` is the $\mathbb{C}$-span of the functions $\varphi$ that are smooth cuspidal automorphic at $\mathrm{pins}$ for $\xi_K$, continuous, invariant under right translation by $\mathrm{pins}.U\,N$, Hecke eigenfunctions with eigenvalue $\Phi.a(v)$ at each $v\notin S_K$ and central eigenfunctions with eigenvalue $\Phi.b(v)$ there; and that `cuspClasses K pins ξK N SK` consists of those eigensystems $\Phi$ of level $N$ with $\Phi.a(v)=\Phi.b(v)=0$ for $v\in S_K$ and nonzero isotypic cusp submodule.
--
--   **Cusp basis data.** A type $\iota$, functions $b:\iota\to(\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ and $\mathrm{cls}:\iota\to$ `HeckeEigensystem K ℂ` are given, with: `hb`, each $\mathrm{cls}(i)$ lies in `cuspClasses K pins ξK N SK` and $b_i$ lies in `isotypicCuspSubmodule K pins ξK N SK (cls i)` $\cap$ `archCutSubmodule K tysK`; `hbn`, $\int_{D_{\alpha,\beta}} b_i\overline{b_i}\,d\mu_{\mathrm{GL}}=1$ for all $i$; `hbo`, $\int_{D_{\alpha,\beta}} b_i\overline{b_j}\,d\mu_{\mathrm{GL}}=0$ for $i\ne j$; `hbs`, for every $\pi$ in `cuspClasses K pins ξK N SK` the fibre $\{i\mid \mathrm{cls}(i)=\pi\}$ is finite and the span of its image under $b$ equals `isotypicCuspSubmodule K pins ξK N SK π` $\cap$ `archCutSubmodule K tysK`; and `hbc` (completeness), every $\varphi$ that is smooth cuspidal automorphic at $\mathrm{pins}$ for $\xi_K$, continuous, invariant under right translation by $\mathrm{pins}.U\,N$, a member of `archCutSubmodule K tysK`, and orthogonal to every $b_i$ over $D_{\alpha,\beta}$, vanishes $\mu_{\mathrm{GL}}$-almost everywhere on $D_{\alpha,\beta}$.
--
--   **Character-pair family.** A countable type $\iota_E$ and families $\mu,\nu:\iota_E\to(\mathbb{A}_K^\times\to\mathbb{C}^\times)$ are given, subject to: unitarity of each $\mu_e$ and $\nu_e$ (`_hμ`, `_hν`, i.e. all values of absolute value $1$); triviality on $K^\times$ (`_hμic`, `_hνic`); continuity (`_hμc`, `_hνc`); the product relation `_hμν`, $\mu_e(z)\nu_e(z)=\xi_K(z)$ for all $e,z$; and separation `_hdist`, for $e\ne e'$ there is $z$ in [`NumberField.TateGlobal.normOneIdeles K`](def/NumberField_TateGlobalZeta.html#L16) (the kernel of `distribHaarChar`) with $\mu_e(z)\ne\mu_{e'}(z)$ or $\nu_e(z)\ne\nu_{e'}(z)$.
--
--   **Induced sections.** Integers $n_E(e)$ and functions $\varphi_{e,j}(s,\cdot)$ for $j\in\mathrm{Fin}(n_E(e))$, $s\in\mathbb{C}$ are given, with the following hypotheses. `_hφE`: each $\varphi_{e,j}(s,\cdot)$ is an induced section for the pair $\big(\mathrm{etaFst}(\mu_e,\alpha_m,s),\mathrm{etaSnd}(\nu_e,\alpha_m,s)\big)=\big(\mu_e\,\alpha_m^{\,s+1/2},\ \nu_e\,\alpha_m^{-(s+1/2)}\big)$, that is $\varphi(bg)=\eta_1(b_{00})\eta_2(b_{11})\varphi(g)$ for $b$ in the adelic Borel subgroup. `_hφEK`: archimedean $K$-finiteness at every infinite place. `_hφEf`: smoothness in the finite directions (`IsKfSmooth`). `_hφEjc`: joint continuity of $(s,g)\mapsto\varphi_{e,j}(s,g)$. `_hφEhol`: complex differentiability of $s\mapsto\varphi_{e,j}(s,g)$ for each $g$. `_hφEKu`: at each infinite place $w$ a single finite-dimensional space $W$ of functions on the row-isometry subgroup `archRowIsometrySubgroup K w` containing all right translates $k\mapsto\varphi_{e,j}(s,gk)$, uniformly in $s$ and $g$. `_hφEflat`: $\varphi_{e,j}(s,k)=\varphi_{e,j}(0,k)$ for $k$ in the adelic maximal compact subgroup. `_hφElev`: right invariance under $\mathrm{principalLevel}(N)\cap\ker(\text{archimedean projection})$. `_hφEty`: membership in `archCutSubmodule K tysK`. `_hφEon`: orthonormality $\int \varphi_{e,i}(0,k)\overline{\varphi_{e,j}(0,k)}\,d($`maximalCompactHaar K`$)=\delta_{ij}$. `_hφEspan`: for each $e$, each $t\in\mathbb{R}$ and each $\varphi_0$ which is an induced section for the pair at $s=it$, continuous, archimedean $K$-finite, invariant under the above level subgroup and in `archCutSubmodule K tysK`, the function $\varphi_0$ lies in the span of the $\varphi_{e,j}(it,\cdot)$, $j\in\mathrm{Fin}(n_E(e))$. `_hpairs`: for every pair $(\mu',\nu')$ of unitary continuous characters trivial on $K^\times$ with $\mu'\nu'=\xi_K$, every $t\in\mathbb{R}$ and every nonzero $\varphi_0$ with the same list of properties at $s=it$, there is $e\in\iota_E$ with $\mu_e=\mu'$ and $\nu_e=\nu'$ on the norm-one ideles.
--
--   **Continuation data.** Sets $O_{e,j}\subseteq\mathbb{C}$ and families $E_{e,j},N_{e,j}:\mathbb{C}\to(\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ are given, and `_hEE` asserts, for all $e$ and $j$: $O_{e,j}$ is open and preconnected; it contains the line $\{\operatorname{Re}s=0\}$ and the half-plane $\{\operatorname{Re}s>1/2\}$; for each $g$ the functions $s\mapsto E_{e,j}(s,g)$ and $s\mapsto N_{e,j}(s,g)$ are analytic on a neighbourhood of $O_{e,j}$; $(s,g)\mapsto E_{e,j}(s,g)$ and $(s,g)\mapsto N_{e,j}(s,g)$ are continuous on $O_{e,j}\times\mathrm{univ}$; for $\operatorname{Re}s>1/2$ and all $g$,
--   $$E_{e,j}(s,g)=\varphi_{e,j}(s,g)+\sum_{\xi\in K}\varphi_{e,j}\big(s,\,w\,n(\xi)\,g\big),$$
--   where $w=$ `adelicWeyl` is the image of $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $n(\xi)=\begin{pmatrix}1&\xi\\0&1\end{pmatrix}$; and for $\operatorname{Re}s>1/2$ and all $g$, $N_{e,j}(s,g)=\int_{\mathbb{A}_K}\varphi_{e,j}\big(s,\,w^{-1}n(x)g\big)\,d($`adelicAddHaar`$)(x)$, the Weyl intertwining integral.
--
--   **Conclusion.** For all $e\in\iota_E$, $j\in\mathrm{Fin}(n_E(e))$, $s\in\mathbb{C}$ with $\operatorname{Re}s>1/2$, and all $i\in\iota$,
--   $$\int_{D_{\alpha,\beta}} E_{e,j}(s,g)\,\overline{b_i(g)}\;d\mu_{\mathrm{GL}}(g)=0.$$
--
--   This is the unfolding step of the classical orthogonality of Eisenstein series to cusp forms, here in the region $\operatorname{Re}s>1/2$ where the continuation $E_{e,j}$ is given by its absolutely convergent Bruhat series over $B(K)\backslash\mathrm{GL}_2(K)$: the pairing of that series against a cusp form of the orthonormal basis reduces, after unfolding, to an integral of the constant term of $b_i$, which vanishes. It is used by [`AutomorphicForm.setIntegral_axis_continuation_mul_conj_cuspBasis_eq_zero_of_mem`](thm.html#AutomorphicForm.setIntegral_axis_continuation_mul_conj_cuspBasis_eq_zero_of_mem), which propagates the vanishing from this half-plane to the whole domain $O_{e,j}$ of the continuation, and thence in the separation of the cuspidal and continuous parts of the spectral expansion over the truncation domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_axis_continuation_mul_conj_cuspBasis_eq_zero_of_re_gt_half.lean

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

theorem AutomorphicForm.setIntegral_axis_continuation_mul_conj_cuspBasis_eq_zero_of_re_gt_half
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
      (e : ιE) (j : Fin (nE e)) (s : ℂ) (_hs : (1 / 2 : ℝ) < s.re) (i : ι),
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, EE e j s g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by sorry
