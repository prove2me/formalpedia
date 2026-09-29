-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_convOp_continuousProjection_eq_mul_setIntegral_prod_tsum_integral_sum_rightConv_axis_continuation
-- name    : AutomorphicForm.exists_forall_setIntegral_convOp_continuousProjection_eq_mul_setIntegral_prod_tsum_integral_sum_rightConv_axis_continuation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/f0b9732e-9168-5caf-b0ce-205463652ccb
-- title:
--   Continuous block of the GL₂ spectral expansion on A× B
-- statement:
--   Throughout, $K$ is a number field, $\mathbb{A}$ its adele ring, and `AdelicGL2 (𝓞 K) K` $=\mathrm{GL}_2(\mathbb{A})$. All automorphic notions below are taken relative to one fixed package of carrier data, namely `productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, whose components are: the Borel $\sigma$-algebra and the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` on $\mathrm{GL}_2(\mathbb{A})$; the domain $D=$ `canonicalTruncationDomain K α β`; the central subgroup $Z=\top\le\mathbb{A}^\times$; the level subgroups $U(M)=$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K` (the $M$-th principal level intersected with the kernel of the archimedean projection); the Hecke elements `heckeGen (𝓞 K) K v`; and, on $\mathbb{A}$, the Borel $\sigma$-algebra together with the additive Haar measure conditioned on the box `adelicBox K`.
--
--   **Global data.** Reals $\alpha,\beta$ with $0<\alpha<\beta$; a set $\Phi_K\subseteq\mathrm{GL}_2(\mathbb{A})$, on which no condition is imposed; reals $c_K,u_K,d_{1K},d_{2K}$ and a finite set $T_K\subseteq\mathrm{GL}_2(\mathbb{A})$ subject to $0<c_K$, $0<d_{1K}$, $d_{1K}<d_{2K}$, and the covering hypothesis `hcovK`: the union $\bigcup_{x\in T_K}\{g x : g\in\mathfrak{S}\}$ of right translates of the centre-cut Siegel set $\mathfrak{S}=$ `centreCutSiegelSet K cK uK d₁K d₂K` — the $g$ whose finite part lies in the finite integral subgroup, whose archimedean local height at every infinite place is at least $c_K$, whose $x$-window square at every infinite place is at most $u_K^2$, and whose archimedean determinant norm at every infinite place lies in $[d_{1K},d_{2K}]$ — covers $\mathrm{GL}_2(\mathbb{A})$ modulo the centre, i.e. for every $g$ there are $\gamma\in\mathrm{GL}_2(K)$ and $z\in\mathbb{A}^\times$ with $\gamma g z$ in that union. Further: a Haar measure $\nu_{Z,K}$ on $\mathbb{A}^\times$ and a set $\Omega_K$ which is a fundamental domain (`hΩK`) for the range of $K^\times\to\mathbb{A}^\times$ acting on $\mathbb{A}^\times$ with respect to $\nu_{Z,K}$; a finite set $S_K$ of finite places of $K$; a homomorphism $\xi_K:\top\to\mathbb{C}^\times$ on the full idele unit group which is continuous (`hξc`), trivial on the principal ideles (`hξt`) and of modulus one (`hξu`); an ideal $N$ of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$ (`hN`); an archimedean type family $\mathrm{tys}_K$ (for each infinite place $w$ a finite list of representations of the row-isometry subgroup at $w$, cutting out the submodule `archCutSubmodule K tysK` $=\bigcap_w\sum_i$ `archTypeSubmoduleAt`). Finally $\alpha_m$ denotes the homomorphism $\mathbb{A}^\times\to\mathbb{R}^\times$ obtained from `distribHaarChar (AdeleRing (𝓞 K) K)` through $\mathbb{R}_{\ge0}\to\mathbb{R}$, and `hαm` asserts that $\alpha_m(x)>0$ for all $x$.
--
--   **Assertion.** There exists $\kappa\in\mathbb{R}$ with $\kappa>0$ such that the identity below holds for all further data as follows.
--
--   *Cuspidal family.* A type $\iota$, functions $b:\iota\to(\mathrm{GL}_2(\mathbb{A})\to\mathbb{C})$ and $\mathrm{cls}:\iota\to$ `HeckeEigensystem K ℂ` (a level ideal $\ne\bot$ together with families $a_v,b_v\in\mathbb{C}$ over the finite places), subject to: `hb`, each $\mathrm{cls}\,i$ is a cusp class for the carrier data, $\xi_K$, $N$, $S_K$ (level $N$; $a_v=b_v=0$ for $v\in S_K$; non-zero isotypic cusp submodule) and $b\,i$ lies in `isotypicCuspSubmodule` for $\mathrm{cls}\,i$ intersected with `archCutSubmodule K tysK`; `hbn`, $\int_D b\,i\cdot\overline{b\,i}=1$; `hbo`, $\int_D b\,i\cdot\overline{b\,j}=0$ for $i\ne j$; `hbs`, for every cusp class $\pi$ the fibre $\{i:\mathrm{cls}\,i=\pi\}$ is finite and the $\mathbb{C}$-span of $b$ over it equals the isotypic cusp submodule of $\pi$ intersected with `archCutSubmodule K tysK`; `hbc` (completeness), every $\varphi$ which is a smooth cuspidal automorphic function for the carrier data and $\xi_K$, continuous, right invariant under $U(N)$, a member of `archCutSubmodule K tysK`, and orthogonal on $D$ to all $b\,i$, vanishes almost everywhere for the Haar measure restricted to $D$. (All integrals over $D$ are with respect to `adelicGLHaar (Fin 2) (𝓞 K) K`.)
--
--   *Eisenstein family.* A countable type $\iota_E$ and characters $\mu,\nu:\iota_E\to(\mathbb{A}^\times\to\mathbb{C}^\times)$, each $\mu_e,\nu_e$ of modulus one, trivial on $K^\times$, continuous, with $\mu_e\nu_e=\xi_K$, and distinct indices separated on the norm-one ideles $\ker(\mathrm{distribHaarChar})$ (`_hμ`, `_hν`, `_hμic`, `_hνic`, `_hμc`, `_hνc`, `_hμν`, `_hdist`). Dimensions $n_E:\iota_E\to\mathbb{N}$ and sections $\varphi_E(e,j,s):\mathrm{GL}_2(\mathbb{A})\to\mathbb{C}$ for $j<n_E(e)$, $s\in\mathbb{C}$, subject to the clauses `_hφE`–`_hφEspan`: each $\varphi_E(e,j,s)$ is an induced section for the pair $\big(\mu_e\,\alpha_m^{\,s+1/2},\ \nu_e\,\alpha_m^{-(s+1/2)}\big)$, i.e. $\varphi(bg)=\eta_1(b_{11})\eta_2(b_{22})\varphi(g)$ for $b$ in the adelic Borel subgroup; it is archimedean $K$-finite at every infinite place and smooth for the finite-adelic subgroup; $(s,g)\mapsto\varphi_E(e,j,s)(g)$ is continuous and $s\mapsto\varphi_E(e,j,s)(g)$ is entire; at each infinite place the right translates under the row-isometry subgroup stay in one finite-dimensional space independent of $s$ and $g$ (`_hφEKu`); on the maximal compact subgroup the sections are independent of $s$ (`_hφEflat`); each is right invariant under $U(N)$ (`_hφElev`) and lies in `archCutSubmodule K tysK` (`_hφEty`); the restrictions to the maximal compact subgroup are orthonormal for `maximalCompactHaar K` (`_hφEon`); and (`_hφEspan`) for every $e$, every $t\in\mathbb{R}$ and every $\varphi_0$ which is an induced section at $s=it$ for $(\mu_e,\nu_e)$, continuous, archimedean $K$-finite, $U(N)$-invariant and in `archCutSubmodule K tysK`, one has $\varphi_0\in\mathrm{span}_{\mathbb{C}}\{\varphi_E(e,j,it)\}_{j<n_E(e)}$. The clause `_hpairs` states exhaustiveness: for any unitary idele class characters $\mu',\nu'$, continuous, with $\mu'\nu'=\xi_K$, and any $t\in\mathbb{R}$ and non-zero $\varphi_0$ induced at $s=it$ for $(\mu',\nu')$, continuous, archimedean $K$-finite, $U(N)$-invariant and in `archCutSubmodule K tysK`, there is $e\in\iota_E$ with $\mu_e=\mu'$ and $\nu_e=\nu'$ on the norm-one ideles.
--
--   *Continuations.* Sets $O_E(e,j)\subseteq\mathbb{C}$ and functions $E_E(e,j,s),N_E(e,j,s)$, subject to `_hEE`: for each $(e,j)$, $O_E(e,j)$ is open and preconnected and contains both the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$; for each $g$ the functions $s\mapsto E_E(e,j,s)(g)$ and $s\mapsto N_E(e,j,s)(g)$ are analytic on a neighbourhood of every point of $O_E(e,j)$; both $(s,g)\mapsto E_E(e,j,s)(g)$ and $(s,g)\mapsto N_E(e,j,s)(g)$ are continuous on $O_E(e,j)\times\mathrm{GL}_2(\mathbb{A})$; and for $\mathrm{Re}\,s>1/2$ one has the Bruhat expansions $E_E(e,j,s)(g)=\varphi_E(e,j,s)(g)+\sum_{\xi\in K}'\varphi_E(e,j,s)\big(w\,u(\xi)\,g\big)$, with $w=$ `adelicWeyl` and $u(\xi)$ the unipotent matrix of $\xi$, and $N_E(e,j,s)(g)=\int_{\mathbb{A}}\varphi_E(e,j,s)\big(w^{-1}u(x)g\big)\,dx$ for the adelic additive Haar measure.
--
--   *Test function.* A continuous $f:\mathrm{GL}_2(\mathbb{A})\to\mathbb{C}$ of compact support which is factorizable (a product of a compactly supported smooth archimedean factor and a compactly supported locally constant finite factor), bi-invariant under $U(N)$ on both sides, and archimedean bi-finite for $\mathrm{tys}_K$ (that is, $x\mapsto f(x^{-1})$ lies in `archCutSubmodule K tysK` and $f$ lies in `archDualCutSubmodule K tysK`).
--
--   *Geometric data and decomposition.* A compact set $C$, measurable sets $A,B\subseteq C$, and functions $u_c,u_r,u_e$ with: $u_c$ automorphic for the carrier data and $\xi_K$ (in the sense of `IsAutomorphicFnAt`) with constant term along the unipotent family vanishing almost everywhere (`_huc`, `_huc0`); $u_r$ automorphic and approximable, for each $\varepsilon>0$, in $L^2$ of the Haar measure restricted to $D$ to within $\varepsilon$ by an automorphic element $r$ of `residualSpan` — the span of the functions $g\mapsto\chi(\det g)$ for characters $\chi$ with $\chi^2=\xi_K$ on $Z$ — (`_hur`, `_hurc`); $u_e$ automorphic and orthogonal on $D$ to every automorphic $h$ whose unipotent constant term vanishes almost everywhere or which lies in `residualSpan` (`_hue`, `_hueo`); and `_hsum`, the automorphisation of the indicator of $B$, namely
--   $$g\mapsto\sum_{q\in\mathrm{GL}_2(K)/Z(\mathrm{GL}_2(K))}^{\text{f}}\int_{\mathbb{A}^\times}\xi_K(w)^{-1}\,\mathbf 1_D\big(\mathbf 1_B\big)\big(z(w)\cdot(\gamma(q)\,g)\big)\,d\nu_{Z,K}(w),$$
--   with $z(\cdot)$ the central scalar, $\gamma(\cdot)$ the global points map, $q$ represented by `Quotient.out` and the outer sum a finite-support sum, agrees almost everywhere, for the Haar measure restricted to $D$, with $u_c+u_r+u_e$.
--
--   **Conclusion.** Under all of the above,
--   $$\int_{A}(\mathrm{conv}_f u_e)(x)\,d\big(\mathrm{adelicGLHaar}|_D\big)(x)=\kappa\int_{A\times B}\ \sum_{e\in\iota_E}'\ \int_{\mathbb{R}}\ \sum_{i,j<n_E(e)}a_{e,ij}(t)\,E_E(e,i,it)(p_1)\,\overline{E_E(e,j,it)(p_2)}\,dt\ \ d\big(\mathrm{adelicGLHaar}|_D\otimes\mathrm{adelicGLHaar}|_D\big)(p),$$
--   where $\mathrm{conv}_f u_e=$ `convOp K f ue` is the right convolution $x\mapsto\int u_e(xy)f(y)\,dy$ against the Haar measure on $\mathrm{GL}_2(\mathbb{A})$, the coefficient is
--   $$a_{e,ij}(t)=\int_{k}\big(\mathrm{rightConv}\,K\,\varphi_E(e,j,it)\,f\big)(k)\ \overline{\varphi_E(e,i,it)(k)}\ d(\mathrm{maximalCompactHaar}\,K)(k),$$
--   integrated over the adelic maximal compact subgroup, and $\kappa$ is coerced into $\mathbb{C}$. Note the index pattern: the coefficient pairs $j$ with the convolved section and $i$ with its conjugate, while the Eisenstein factors carry $i$ at the first variable and $j$ at the second.
--
--   This is the continuous (Eisenstein) block of the $L^2$ spectral expansion of the automorphic kernel for $\mathrm{GL}_2$ over a number field, in the rectangle form: the integral over $A$ of $R(f)$ applied to the continuous component of the automorphised indicator of $B$ is expressed, up to one positive constant, as a double integral over $A\times B$ of the Eisenstein bilinear kernel along the unitary axis. It feeds the aggregation statement [`AutomorphicForm.exists_forall_setIntegral_prod_restrict_canonicalTruncationDomain_finsum_integral_centralScalar_sub_tsum_convOp_sub_finsum_chiDet_eq_mul_setIntegral_tsum_integral_sum_rightConv_axis_continuation`](thm.html#AutomorphicForm.exists_forall_setIntegral_prod_restrict_canonicalTruncationDomain_finsum_integral_centralScalar_sub_tsum_convOp_sub_finsum_chiDet_eq_mul_setIntegral_tsum_integral_sum_rightConv_axis_continuation), where the cuspidal, residual and continuous blocks are combined.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setIntegral_convOp_continuousProjection_eq_mul_setIntegral_prod_tsum_integral_sum_rightConv_axis_continuation.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_setIntegral_convOp_continuousProjection_eq_mul_setIntegral_prod_tsum_integral_sum_rightConv_axis_continuation
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
    ∃ κ : ℝ, 0 < κ ∧
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
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
    ∀ (C : Set (AdelicGL2 (𝓞 K) K)) (_hC : IsCompact C)
      (A : Set (AdelicGL2 (𝓞 K) K)) (_hA : A ⊆ C) (_hAm : MeasurableSet A)
      (B : Set (AdelicGL2 (𝓞 K) K)) (_hB : B ⊆ C) (_hBm : MeasurableSet B)
      (uc ur ue : AdelicGL2 (𝓞 K) K → ℂ)
      (_huc : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK uc) (_huc0 : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 uc g = 0))
      (_hur : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ur)
      (_hurc : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (ur - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hue : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ue)
      (_hueo : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        ((∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 h g = 0) ∨ h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ue g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (_hsum : (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator (B.indicator fun _ => (1 : ℂ))
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] uc + ur + ue),
    ∫ x in A, convOp K f ue x ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) =
      (κ : ℂ) * ∫ p in A ×ˢ B, (∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            (EE e i ((t : ℂ) * Complex.I) p.1 * conj (EE e j ((t : ℂ) * Complex.I) p.2))) ∂(((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)).prod ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))) := by sorry
