-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_eq_mul_integral_sum_rightConv_mul_setIntegral_lambdaT_axis_continuation
-- name    : AutomorphicForm.exists_forall_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_eq_mul_integral_sum_rightConv_mul_setIntegral_lambdaT_axis_continuation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/87830222-5e45-5823-aa89-af61d44adbc9
-- title:
--   Integrated continuous-spectrum identity for the truncated GL₂ kernel
-- statement:
--   Throughout, $K$ is a number field, $\mathbb A=\mathbb A_K$ its adele ring, $G=GL_2(\mathbb A)$ (the type `AdelicGL2 (𝓞 K) K`), $\|\cdot\|$ the idele norm [`NumberField.TateGlobal.ideleNorm K`](def/NumberField_TateGlobalZeta.html#L19) (the module of the distributive Haar character), and $\Phi_0=$ [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32). Write $\iota_{\mathrm{gl}}$ for `globalPoints`, $u(x)$ for the unipotent matrix `unipotentGL2 x`, $z\mapsto zI_2$ for `centralScalar`, and $\mathrm{pins}(\Phi)$ for `productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, the carrier data whose group measure is the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K`, whose level subgroups are the principal level subgroups at $M$ intersected with the kernel of the archimedean projection, whose Hecke generators are `heckeGen`, whose central subgroup is all of $\mathbb A^\times$, and whose adelic measure $\nu$ is the additive Haar measure of $\mathbb A$ conditioned to the adelic box.
--
--   The fixed data are: reals $\alpha,\beta$ with $0<\alpha$ and $\alpha<\beta$; a set $\Phi_K\subseteq G$; reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}<d_{2K}$ and a finite set $T_K\subseteq G$ such that (`hcovK`) the union $\bigcup_{x\in T_K}(\cdot\, x)\,[\,$`centreCutSiegelSet K cK uK d₁K d₂K`$\,]$ covers $G$ modulo global points and the centre, i.e. for every $g\in G$ there are $\gamma\in GL_2(K)$ and $z\in\mathbb A^\times$ with $\iota_{\mathrm{gl}}(\gamma)\,g\,(zI_2)$ in that union; a Haar measure $\nu_{ZK}$ on $\mathbb A^\times$ together with a set $\Omega_K$ that is a fundamental domain for the image of $K^\times$ in $\mathbb A^\times$ with respect to $\nu_{ZK}$; a finite set $S_K$ of finite places of $K$; a homomorphism $\xi_K$ from the top subgroup of $\mathbb A^\times$ to $\mathbb C^\times$ which is continuous (`hξc`), trivial on the image of $K^\times$ (`hξt`) and of modulus $\|\xi_K(z)\|=\|z\|^{w}$ for a fixed real $w$ (`hξw`); an ideal $N$ of $\mathcal O_K$ such that every place dividing $N$ lies in $S_K$ (`hN`); and an archimedean type family $\mathrm{tys}_K$, i.e. for each infinite place a finite list of representations of the row-isometry subgroup, giving the cut submodule `archCutSubmodule K tysK`. Finally $\alpha_m:\mathbb A^\times\to\mathbb R^\times$ denotes the module character obtained from the distributive Haar character of $\mathbb A$, and `hαm` asserts $\alpha_m(x)>0$ for all $x$.
--
--   Under these assumptions there exists $\kappa\in\mathbb R$ with $\kappa>0$ such that the following holds for all further data.
--
--   Cuspidal data: a type $\iota$, functions $b_i:G\to\mathbb C$ and Hecke eigensystems $\mathrm{cls}(i)$ ($i\in\iota$) with (`hb`) each $\mathrm{cls}(i)$ a cusp class for $\mathrm{pins}(\Phi_0)$, $\xi_K$, $N$, $S_K$ — that is, of level $N$, with $a_v=b_v=0$ for $v\in S_K$ and non-zero isotypic cusp submodule — and $b_i$ in that isotypic cusp submodule intersected with `archCutSubmodule K tysK`; orthonormality (`hbn`) $\int_{\Phi_0}b_i\overline{b_i}=1$ and orthogonality (`hbo`) $\int_{\Phi_0}b_i\overline{b_j}=0$ for $i\neq j$, both against `adelicGLHaar`; class-wise completeness (`hbs`): for every cusp class $\pi$ the fibre $\{i\mid \mathrm{cls}(i)=\pi\}$ is finite and the $\mathbb C$-span of the corresponding $b_i$ is the isotypic cusp submodule of $\pi$ intersected with the arch cut submodule; and completeness (`hbc`): any $\varphi:G\to\mathbb C$ which is a smooth cuspidal automorphic function for $\mathrm{pins}(\Phi_0)$ and $\xi_K$, continuous, right invariant under the level subgroup at $N$, lies in the arch cut submodule and is orthogonal over $\Phi_0$ to every $b_i$, vanishes almost everywhere on $\Phi_0$.
--
--   Eisenstein data: a countable type $\iota_E$ and families of characters $\mu_e,\nu_e:\mathbb A^\times\to\mathbb C^\times$ which are unitary (`_hμ`, `_hν`), trivial on $K^\times$ (`_hμic`, `_hνic`), continuous (`_hμc`, `_hνc`), satisfy $\mu_e(z)\nu_e(z)\|z\|^{w}=\xi_K(z)$ for all $z$ (`_hμν`), and are pairwise distinct on the norm-one ideles (`_hdist`). Further, integers $n_E(e)$ and sections $\varphi_{e,j,s}:G\to\mathbb C$ for $j<n_E(e)$, $s\in\mathbb C$, subject to the following group of hypotheses: each $\varphi_{e,j,s}$ is an induced section for the pair $\big(\mu_e\|\cdot\|^{s+1/2},\,\nu_e\|\cdot\|^{-(s+1/2)}\big)$, meaning $\varphi(bg)=\eta_1(b_{11})\eta_2(b_{22})\varphi(g)$ for $b$ in the adelic Borel (`_hφE`); archimedean $K$-finite (`_hφEK`); smooth for the finite-adelic subgroup (`_hφEf`); jointly continuous in $(s,g)$ (`_hφEjc`); holomorphic in $s$ for each $g$ (`_hφEhol`); uniformly $K$-finite at each infinite place, the right translates lying in one finite-dimensional space $W$ independent of $s$ and $g$ (`_hφEKu`); flat, i.e. $\varphi_{e,j,s}(k)=\varphi_{e,j,0}(k)$ for $k$ in the adelic maximal compact (`_hφEflat`); right invariant under the principal level at $N$ intersected with the finite-adelic subgroup (`_hφElev`); in the arch cut submodule (`_hφEty`); orthonormal over the maximal compact against `maximalCompactHaar K` (`_hφEon`); and spanning, for each $e$ and each real $t$, the space of continuous arch-$K$-finite level-$N$ induced sections at $s=it$ lying in the arch cut submodule (`_hφEspan`). The hypothesis `_hpairs` asserts exhaustiveness of the family of pairs: whenever $\mu',\nu'$ are continuous unitary idele class characters with $\mu'(z)\nu'(z)\|z\|^{w}=\xi_K(z)$ and some non-zero continuous arch-$K$-finite level-$N$ section $\varphi_0$ in the arch cut submodule is induced from $\big(\mu'\|\cdot\|^{it+1/2},\nu'\|\cdot\|^{-(it+1/2)}\big)$, there is an $e$ with $\mu_e=\mu'$ and $\nu_e=\nu'$ on the norm-one ideles. Finally, sets $O_{e,j}\subseteq\mathbb C$ and families $E_{e,j,s},N_{e,j,s}:G\to\mathbb C$ with (`_hEE`, nine clauses) $O_{e,j}$ open and preconnected, containing both the imaginary axis $\{\operatorname{Re}s=0\}$ and the half-plane $\{\operatorname{Re}s>1/2\}$; $s\mapsto E_{e,j,s}(g)$ and $s\mapsto N_{e,j,s}(g)$ analytic on a neighbourhood of $O_{e,j}$ for each $g$; both jointly continuous on $O_{e,j}\times G$; and, for $\operatorname{Re}s>1/2$, $E_{e,j,s}(g)=\varphi_{e,j,s}(g)+\sum'_{\xi\in K}\varphi_{e,j,s}\big(w_{\mathbb A}\,u(\xi)\,g\big)$ with $w_{\mathbb A}=$ `adelicWeyl`, and $N_{e,j,s}(g)$ the Weyl intertwining integral $\int_{\mathbb A}\varphi_{e,j,s}(w_{\mathbb A}^{-1}u(x)g)\,dx$ against the additive Haar measure of $\mathbb A$.
--
--   Test function: a continuous $f:G\to\mathbb C$ with compact support which is factorizable (`IsFactorizableTestFn`: $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with $f_\infty$ smooth of compact support in the matrix entries and $f_{\mathrm{fin}}$ locally constant of compact support), bi-invariant under the principal level at $N$ intersected with the finite-adelic subgroup, and archimedean bi-finite for $\mathrm{tys}_K$ (`IsArchBiFinite`: $g\mapsto f(g^{-1})$ lies in the arch cut submodule and $f$ in the arch dual cut submodule).
--
--   For such data there exists $R_0\in\mathbb R$ such that for every $R\geq R_0$ the four assertions below hold. Write $\Lambda^{R}$ for the truncation operator `lambdaT` formed with the measurable structure and measure of $\mathrm{pins}(\Phi_K)$ on $\mathbb A$ (the Borel structure and the additive Haar measure conditioned to the adelic box), the unipotent embedding $t\mapsto u(t)$, the adelic height [`NumberField.AdelicHeight.adelicHeight K`](def/NumberField_AdelicHeight.html#L158) and threshold $e^{R}$; thus $\Lambda^{R}\psi=\psi-\mathbf 1_{\mathrm{highSet}}\cdot(\text{constant term of }\psi)$. Put $v_{\alpha\beta}=\nu_{ZK}\big(\Omega_K\cap\{z\mid \|\det(zI_2)\|\in[\alpha,\beta]\}\big)$ and let $V=\mathrm{vol}_{\mathrm{adelicGLHaar}}(\Phi_0)$. The three kernels occurring, each truncated in the second variable and then evaluated on the diagonal at $x$, are
--   $$K^{\mathrm{fold}}_x(y')=\sum^{\mathrm f}_{q\in GL_2(K)/Z(GL_2(K))}\int_{\mathbb A^\times}\xi_K(z)\,f\big(x^{-1}\,\iota_{\mathrm{gl}}(q_{\mathrm{out}})\,(zI_2\,y')\big)\,d\nu_{ZK}(z),$$
--   $$K^{\mathrm{cusp}}_x(y')=v_{\alpha\beta}\sum_{i\in\iota}{}'\,(\mathrm{convOp}_f b_i)(x)\,\overline{b_i(y')},\qquad (\mathrm{convOp}_f b_i)(x)=\int_G b_i(xg)f(g)\,dg,$$
--   $$K^{\mathrm{res}}_x(y')=\frac{v_{\alpha\beta}}{V}\sum^{\mathrm f}_{\chi}\Big(\int_G f(g)\,\chi(\det g)\,dg\Big)\,\chi(\det x)\,\chi^{-1}(\det y'),$$
--   the last finite sum being over the continuous characters $\chi$ of $\mathbb A^\times$ with $\chi^2=\xi_K$ on all of $\mathbb A^\times$ and $\chi$ trivial on the image of $K^\times$. Set, for $e\in\iota_E$ and $t\in\mathbb R$,
--   $$a^{e}_{ij}(t)=\int_{K_{\max}}\Big(\mathrm{rightConv}\big(g\mapsto\varphi_{e,j,it}(g)\,\|\det g\|^{w/2}\big)\,f\Big)(k)\;\overline{\varphi_{e,i,it}(k)}\,d\mu_{K_{\max}}(k),$$
--   with $K_{\max}$ the adelic maximal compact and $\mu_{K_{\max}}$ its Haar measure, and
--   $$G^{e,R}_{ij}(t)=\int_{\Phi_0}\Lambda^{R}E_{e,i,it}(x)\;\overline{\Lambda^{R}E_{e,j,it}(x)}\,dx .$$
--
--   The four assertions are: (i) the function $x\mapsto \Lambda^{R}K^{\mathrm{fold}}_x(x)-\Lambda^{R}K^{\mathrm{cusp}}_x(x)-\Lambda^{R}K^{\mathrm{res}}_x(x)$ is integrable on $\Phi_0$ against `adelicGLHaar`; (ii) for each $e\in\iota_E$ the function $t\mapsto\sum_{i,j<n_E(e)}a^{e}_{ij}(t)\,G^{e,R}_{ij}(t)$ is integrable on $\mathbb R$; (iii) the family $e\mapsto\int_{\mathbb R}\big\|\sum_{i,j<n_E(e)}a^{e}_{ij}(t)\,G^{e,R}_{ij}(t)\big\|\,dt$ is summable; and (iv) the identity
--   $$\int_{\Phi_0}\Big(\Lambda^{R}K^{\mathrm{fold}}_x(x)-\Lambda^{R}K^{\mathrm{cusp}}_x(x)-\Lambda^{R}K^{\mathrm{res}}_x(x)\Big)dx=\kappa\sum_{e\in\iota_E}{}'\int_{\mathbb R}\sum_{i,j<n_E(e)}a^{e}_{ij}(t)\,G^{e,R}_{ij}(t)\,dt$$
--   holds, with $\kappa$ the constant fixed before all the spectral data, the test function and $R$.
--
--   This is the integrated form, over the truncation domain $\Phi_0$, of the continuous-spectrum expansion of the Arthur–Selberg kernel for $GL_2$ over a number field: the diagonal integral of the truncated kernel with its cuspidal and residual blocks removed is expressed as a single constant times an absolutely convergent sum over ordered pairs of unitary idele class characters of integrals along the unitary axis of matrix coefficients of $f$ against the Gram matrix of truncated Eisenstein series, the central character $\xi_K$ being allowed arbitrary modulus $\|\cdot\|^{w}$ rather than unitary. It feeds the passage to the limit $R\to\infty$ in [`AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_sub_mul`](thm.html#AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_sub_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_eq_mul_integral_sum_rightConv_mul_setIntegral_lambdaT_axis_continuation.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_eq_mul_integral_sum_rightConv_mul_setIntegral_lambdaT_axis_continuation
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
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ)) :
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
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ),
        ((μ e z : ℂˣ) : ℂ) * ((ν e z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
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
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          ((μ' z : ℂˣ) : ℂ) * ((ν' z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) →
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
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      IntegrableOn (fun x => ((@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                  ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K q.out *
                      (AutomorphicForm.centralScalar (𝓞 K) K z * y')) ∂νZK)
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
                  ∑' i : ι, convOp K f (b i) x * conj (b i y'))
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
                  ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y'))
                x)))
        (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) ∧
      (∀ e : ιE, Integrable (fun t : ℝ => ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g *
                (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) f (k : AdelicGL2 (𝓞 K) K) *
              conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
            (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (EE e i ((t : ℂ) * Complex.I))
                x) *
              conj (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (EE e j ((t : ℂ) * Complex.I))
                x)
              ∂(adelicGLHaar (Fin 2) (𝓞 K) K)))) ∧
      (Summable fun e : ιE => ∫ t : ℝ, ‖∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g *
                (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) f (k : AdelicGL2 (𝓞 K) K) *
              conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
            (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (EE e i ((t : ℂ) * Complex.I))
                x) *
              conj (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (EE e j ((t : ℂ) * Complex.I))
                x)
              ∂(adelicGLHaar (Fin 2) (𝓞 K) K))‖) ∧
      (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
          ((@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                  ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K q.out *
                      (AutomorphicForm.centralScalar (𝓞 K) K z * y')) ∂νZK)
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
                  ∑' i : ι, convOp K f (b i) x * conj (b i y'))
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
                  ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y'))
                x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
      (κ : ℂ) * ∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g *
                (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) f (k : AdelicGL2 (𝓞 K) K) *
              conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
            (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (EE e i ((t : ℂ) * Complex.I))
                x) *
              conj (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (EE e j ((t : ℂ) * Complex.I))
                x)
              ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by sorry
