-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_sigmaAdelicAct_symm_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_of_norm_eq_one
-- name    : AutomorphicForm.exists_forall_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_sigmaAdelicAct_symm_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_of_norm_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/af1ab402-c0f6-58f8-816d-6cbed03c49d8
-- title:
--   Integrated truncated twisted kernel and its continuous-spectrum expansion
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L$ a $K$-algebra, and $G$ denotes $\mathrm{GL}_2(\mathbb{A}_L)$ (`AdelicGL2 (𝓞 L) L`), equipped with its Borel structure and Haar measure `adelicGLHaar (Fin 2) (𝓞 L) L`; the idele group $\mathbb{A}_L^\times$ carries a measurable and Borel structure and a Haar measure $\nu_{Z_L}$.
--
--   **Geometric and central data.** Real numbers $\alpha,\beta$ with $0<\alpha$ and $\alpha<\beta$ cut out the slab $\{g\in G : \|\det g\|_{\mathbb{A}_L}\in[\alpha,\beta]\}$, where $\|\cdot\|_{\mathbb{A}_L}$ is [`NumberField.TateGlobal.ideleNorm L`](def/NumberField_TateGlobalZeta.html#L19), the module character of $\mathbb{A}_L$. A set $\Phi_L\subseteq G$ is assumed to lie in this slab (`hΦs`) and to be a fundamental domain for the image of $\mathrm{GL}_2(L)$ under `globalPoints` acting on the slab, for the Haar measure restricted to the slab (`hΦ`). A set $\Omega_L\subseteq\mathbb{A}_L^\times$ is a fundamental domain for the image of $L^\times$ for $\nu_{Z_L}$ (`hΩL`). Further data: a Galois descent datum $D$ for the adeles of $L$ over $K$ (a homomorphism from $K$-automorphisms of $L$ to ring automorphisms of $\mathbb{A}_L$, compatible with the action on principal adeles and continuous), an automorphism $\sigma\in\mathrm{Aut}_K(L)$, a finite set $S_L$ of height-one primes of $\mathcal{O}_L$, a character $\xi$ of the full subgroup $\top\le\mathbb{A}_L^\times$ with values in $\mathbb{C}^\times$ which is continuous (`hξc`), trivial on principal ideles (`hξt`) and unitary (`hξu`), an ideal $N$ of $\mathcal{O}_L$ all of whose prime divisors lie in $S_L$ (`hN`), and an archimedean type family $\mathrm{tys}_L$ (a finite list of representations of the row-isometry group at each infinite place, cutting out the submodule `archCutSubmodule L tysL`). Finally, reals $c,u,d_1,d_2$ with $0<c$, a compact set $T_c\subseteq G$, and a second set $\Phi_0\subseteq G$ contained in $\bigcup_{y\in T_c}\,\mathrm{(centre\text{-}cut\ Siegel\ set)}\cdot y$ for the parameters $c,u,d_1,d_2$ (`hΦ₀S`), contained in the slab (`hΦ₀s`), and again a fundamental domain for $\mathrm{GL}_2(L)$ on the slab (`hΦ₀`).
--
--   Write $\alpha_m$ for the module character $\mathbb{A}_L^\times\to\mathbb{R}^\times$ obtained from `distribHaarChar` composed with $\mathbb{R}_{\ge0}\to\mathbb{R}$, and assume its values are positive ($h\alpha_m$). Write $\Lambda^{T}$ for the truncation operator [`AutomorphicForm.lambdaT`](def/AutomorphicForm_TruncationOperator.html#L48), which subtracts from a function its constant term along the upper unipotent matrices — integrated against the Haar measure of $\mathbb{A}_L$ conditioned on the adelic box, this being the measure component of the carrier pins `productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)` — on the region where [`NumberField.AdelicHeight.adelicHeight L`](def/NumberField_AdelicHeight.html#L158) exceeds $T$; in the conclusion $T=e^{R}$.
--
--   Under these assumptions there exists $\kappa\in\mathbb{R}$ with $\kappa>0$, such that the following holds for every choice of spectral data as follows (so $\kappa$ is uniform in all of it).
--
--   **Cuspidal family.** A type $\iota$, functions $b_i:G\to\mathbb{C}$ and Hecke eigensystems $\mathrm{cls}(i)$ over $\mathbb{C}$ for $L$, subject to: `hb`, each $\mathrm{cls}(i)$ is a cusp class for the pins `productionPinsOf L (canonicalTruncationDomain L α β) (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v) (adelicBox L)` with central character $\xi$, level $N$ and bad set $S_L$ (that is, its level is $N$, its Hecke and central parameters vanish on $S_L$, and its isotypic cuspidal submodule is non-zero), and $b_i$ lies in that isotypic cuspidal submodule intersected with `archCutSubmodule L tysL`; `hbn` and `hbo`, the $b_i$ are orthonormal for the Hermitian pairing given by integration over the canonical truncation domain $\Phi_c=$ `canonicalTruncationDomain L α β` of the slab; `hbs`, for each cusp class $\pi$ the fibre $\{i:\mathrm{cls}(i)=\pi\}$ is finite and the $b_i$ over it span the corresponding isotypic cuspidal submodule cut by the archimedean types; `hbc`, completeness: any $\varphi:G\to\mathbb{C}$ which is a smooth cuspidal automorphic function at these pins with central character $\xi$, continuous, right invariant under `principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L`, lying in the archimedean cut submodule, and orthogonal to every $b_i$ over $\Phi_c$, vanishes almost everywhere on $\Phi_c$.
--
--   **Eisenstein data.** A countable type $\iota_E$, families of characters $\mu_e,\nu_e$ of $\mathbb{A}_L^\times$ which are unitary, trivial on principal ideles, continuous, satisfy $\mu_e\nu_e=\xi$ pointwise, and are pairwise separated already on the norm-one ideles; integers $n_E(e)$ and sections $\varphi_{e,j}(s,\cdot)$ for $j<n_E(e)$, subject to the hypotheses (named `_hφE`, `_hφEK`, `_hφEf`, `_hφEjc`, `_hφEhol`, `_hφEKu`, `_hφEflat`, `_hφElev`, `_hφEty`, `_hφEon`, `_hφEspan`, summarised here) that each $\varphi_{e,j}(s,\cdot)$ is an induced section for the pair of characters $\eta_1=\mu_e\,\alpha_m^{s+1/2}$, $\eta_2=\nu_e\,\alpha_m^{-(s+1/2)}$ relative to the adelic Borel subgroup, is archimedean $K$-finite and $K_f$-smooth, depends jointly continuously on $(s,g)$ and holomorphically on $s$, has finite-dimensional span of right translates under each archimedean row-isometry subgroup, is independent of $s$ on the adelic maximal compact subgroup, is right invariant under `principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L`, lies in the archimedean cut submodule, is orthonormal in $j$ for the Haar measure `maximalCompactHaar L` of the maximal compact subgroup, and that for each $e$ and each $t\in\mathbb{R}$ the $\varphi_{e,j}(it,\cdot)$ span all such sections on the line $\mathrm{Re}\,s=0$; together with `_hpairs`, that every pair of continuous unitary idele class characters with product $\xi$ admitting a non-zero section of this kind on some vertical line agrees on the norm-one ideles with some $(\mu_e,\nu_e)$. Finally, sets $O_{e,j}\subseteq\mathbb{C}$ and functions $E_{e,j}(s,\cdot)$, $N_{e,j}(s,\cdot)$ with the nine-clause package `_hEE`: $O_{e,j}$ is open, preconnected and contains both the imaginary axis and the half-plane $\mathrm{Re}\,s>1/2$; for each $g$ both $s\mapsto E_{e,j}(s,g)$ and $s\mapsto N_{e,j}(s,g)$ are analytic on a neighbourhood of $O_{e,j}$; both are continuous on $O_{e,j}\times G$; and for $\mathrm{Re}\,s>1/2$ one has the Eisenstein expansion $E_{e,j}(s,g)=\varphi_{e,j}(s,g)+\sum_{\zeta\in L}\varphi_{e,j}\bigl(s,\,w\,u(\zeta)\,g\bigr)$ (with $w$ the adelic Weyl element and $u(\zeta)$ the principal unipotent matrix) and $N_{e,j}(s,\cdot)=$ the Weyl intertwining integral of $\varphi_{e,j}(s,\cdot)$ against the additive Haar measure of $\mathbb{A}_L$.
--
--   **Test function.** A continuous, compactly supported $f:G\to\mathbb{C}$ which is factorizable (a product of a smooth compactly supported archimedean factor and a locally constant compactly supported finite factor), bi-invariant under `principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L`, and archimedean bi-finite for $\mathrm{tys}_L$ (that is, $x\mapsto f(x^{-1})$ lies in the archimedean cut submodule and $f$ lies in the dual cut submodule).
--
--   **Conclusion.** There exists $R_0\in\mathbb{R}$ such that for every $R\ge R_0$, with $T=e^{R}$, the following four assertions hold. Write $b_{\mathrm{vol}}=\nu_{Z_L}\bigl(\Omega_L\cap\{z:\|\det(z\cdot 1_2)\|\in[\alpha,\beta]\}\bigr)$ for the band volume, $V_c$ for the Haar volume of $\Phi_c$, $\sigma_{\mathbb{A}}^{-1}$ for the automorphism of $G$ induced by $D$ at $\sigma^{-1}$ (`sigmaAdelicAct K L D σ.symm`), and $\mathcal{D}(x)$ for the difference
--   $$\Lambda^{T}\!\Bigl[y\mapsto \textstyle\sum^{\mathrm{f}}_{q\in \mathrm{GL}_2(L)/Z}\int \xi(z)\,f\bigl(x^{-1}\gamma_q\,(z\cdot 1_2)\,y\bigr)\,d\nu_{Z_L}(z)\Bigr](\sigma_{\mathbb{A}}^{-1}x) - \Lambda^{T}\!\Bigl[y\mapsto b_{\mathrm{vol}}\textstyle\sum_i (f*b_i)(x)\,\overline{b_i(y)}\Bigr](\sigma_{\mathbb{A}}^{-1}x) - \Lambda^{T}\!\Bigl[y\mapsto \tfrac{b_{\mathrm{vol}}}{V_c}\textstyle\sum^{\mathrm{f}}_{\chi}\bigl(\int f(g)\chi(\det g)\,dg\bigr)\chi(\det x)\,\chi^{-1}(\det y)\Bigr](\sigma_{\mathbb{A}}^{-1}x),$$
--   where $\gamma_q$ is the image in $G$ of a chosen representative of the class $q$ in $\mathrm{GL}_2(L)$ modulo its centre, the first sum is a finite sum over that quotient, $(f*b_i)(x)=\int b_i(xg)f(g)\,dg$ is `convOp L f (b i)`, and the last sum is a finite sum over those continuous characters $\chi$ of $\mathbb{A}_L^\times$ which are trivial on principal ideles and satisfy $\chi(z)^2=\xi(z)$ for all $z$.
--
--   (i) $\mathcal{D}$ is integrable on $\Phi_0$ for the Haar measure of $G$.
--
--   (ii) For each $e\in\iota_E$ the function
--   $$t\mapsto \sum_{i,j<n_E(e)}\Bigl(\int_{K_{\max}} \bigl(\varphi_{e,j}(it,\cdot)*f\bigr)(k)\,\overline{\varphi_{e,i}(it,k)}\,dk\Bigr)\Bigl(\int_{\Phi_0}\Lambda^{T}\bigl[E_{e,i}(it,\cdot)\bigr](x)\,\overline{\Lambda^{T}\bigl[y\mapsto E_{e,j}(it,\sigma_{\mathbb{A}}^{-1}y)\bigr](x)}\,dx\Bigr)$$
--   is integrable on $\mathbb{R}$; here $K_{\max}$ is the adelic maximal compact subgroup with its Haar measure, and $(\varphi*f)(k)=\int\varphi(kx)f(x)\,dx$ is `rightConv`.
--
--   (iii) The function $e\mapsto\int_{\mathbb{R}}\bigl\|\,\cdot\,\bigr\|\,dt$, the integral over $t$ of the norm of the expression displayed in (ii), is summable over $\iota_E$.
--
--   (iv) $\displaystyle\int_{\Phi_0}\mathcal{D}(x)\,dx \;=\;\kappa\sum_{e\in\iota_E}\int_{\mathbb{R}}\sum_{i,j<n_E(e)}\Bigl(\int_{K_{\max}}\bigl(\varphi_{e,j}(it,\cdot)*f\bigr)(k)\,\overline{\varphi_{e,i}(it,k)}\,dk\Bigr)\Bigl(\int_{\Phi_0}\Lambda^{T}\bigl[E_{e,i}(it,\cdot)\bigr](x)\,\overline{\Lambda^{T}\bigl[y\mapsto E_{e,j}(it,\sigma_{\mathbb{A}}^{-1}y)\bigr](x)}\,dx\Bigr)\,dt.$
--
--   The truncation operator in (i), (ii), (iii) and (iv) is the one attached to the carrier pins built from $\Phi_L$, the level-one subgroups and the Hecke generators; only the measure-theoretic components of that record (the Borel structure of $\mathbb{A}_L$ and the Haar measure conditioned on the adelic box) enter $\Lambda^{T}$.
--
--   This is the continuous (Eisenstein) part of the $\sigma$-twisted trace formula for $\mathrm{GL}_2$ over $L$ relative to $K$: after subtracting the cuspidal and one-dimensional kernels from the geometric kernel of $f$, the truncated remainder integrated over the twisted diagonal $x\mapsto(x,\sigma_{\mathbb{A}}^{-1}x)$ in a Siegel-bounded fundamental domain is expressed, up to a positive constant independent of the spectral data and of $f$, as the integral over the unitary axis of the local Eisenstein inner products against truncated Eisenstein series. It feeds the twisted continuous-term package [`AutomorphicForm.exists_forall_setIntegral_lambdaT_sigmaAdelicAct_sub_twistedConvOp_sub_chiDet_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_sigmaAdelicAct`](thm.html#AutomorphicForm.exists_forall_setIntegral_lambdaT_sigmaAdelicAct_sub_twistedConvOp_sub_chiDet_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_sigmaAdelicAct) on the route to base change and the Langlands–Tunnell theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_sigmaAdelicAct_symm_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_of_norm_eq_one.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_forall_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_sigmaAdelicAct_symm_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_of_norm_eq_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξu : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξu ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξu ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (hξu : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ‖((ξu ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    let αm : (AdeleRing (𝓞 L) L)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits
    letI := adeleBorel (𝓞 L) L
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ κ : ℝ, 0 < κ ∧
    ∀
      (ι : Type) (b : ι → AdelicGL2 (𝓞 L) L → ℂ) (cls : ι → HeckeEigensystem L ℂ)
      (hb : ∀ i, cls i ∈ cuspClasses L
            (productionPinsOf L (AutomorphicForm.canonicalTruncationDomain L α β)
            (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξu N SL ∧
          b i ∈ isotypicCuspSubmodule L
            (productionPinsOf L (AutomorphicForm.canonicalTruncationDomain L α β)
            (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξu N SL (cls i) ⊓ archCutSubmodule L tysL)
      (hbn : ∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain L α β,
          b i g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 1)
      (hbo : ∀ i j, i ≠ j → ∫ g in AutomorphicForm.canonicalTruncationDomain L α β,
          b i g * conj (b j g) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 0)
      (hbs : ∀ π ∈ cuspClasses L
            (productionPinsOf L (AutomorphicForm.canonicalTruncationDomain L α β)
            (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξu N SL,
          {i | cls i = π}.Finite ∧
          Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule L
            (productionPinsOf L (AutomorphicForm.canonicalTruncationDomain L α β)
            (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξu N SL π ⊓ archCutSubmodule L tysL)
      (hbc : ∀ φ : AdelicGL2 (𝓞 L) L → ℂ,
          IsSmoothCuspAutomorphicFnAt L
            (productionPinsOf L (AutomorphicForm.canonicalTruncationDomain L α β)
            (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξu φ →
          Continuous φ →
          (∀ g : AdelicGL2 (𝓞 L) L, ∀ u ∈
            (productionPinsOf L (AutomorphicForm.canonicalTruncationDomain L α β)
            (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)).U N, φ (g * u) = φ g) →
          φ ∈ archCutSubmodule L tysL →
          (∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain L α β,
              φ g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 0) →
          φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 L) L).restrict (AutomorphicForm.canonicalTruncationDomain L α β)] 0)
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 L) L)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 L) L (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 L) L (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 L) L (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 L) L (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 L) L)ˣ), μ e z * ν e z = ξu ⟨z, Subgroup.mem_top z⟩)
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles L,
        μ e z ≠ μ e' z ∨ ν e z ≠ ν e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 L) L (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite L (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth L (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 L) L => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 L) L), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace L), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
          (fun k : ↥(archRowIsometrySubgroup L w) => φE e j s (g * (k : AdelicGL2 (𝓞 L) L))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact L),
        φE e j s (k : AdelicGL2 (𝓞 L) L) = φE e j 0 (k : AdelicGL2 (𝓞 L) L))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
        ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule L tysL)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 L) L) * conj (φE e j 0 (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 L) L → ℂ),
        IsInducedSection (𝓞 L) L (etaFst (μ e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (ν e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite L φ₀ →
        (∀ (g : AdelicGL2 (𝓞 L) L), ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule L tysL →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (_hpairs : ∀ (μ' ν' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 L) L μ' → IsUnitaryChar (𝓞 L) L ν' →
        IsIdeleClassChar (𝓞 L) L μ' → IsIdeleClassChar (𝓞 L) L ν' →
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((μ' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ν' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 L) L)ˣ, μ' z * ν' z = ξu ⟨z, Subgroup.mem_top z⟩) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 L) L → ℂ),
        IsInducedSection (𝓞 L) L (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite L φ₀ →
        (∀ (g : AdelicGL2 (𝓞 L) L), ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule L tysL → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles L, μ e z = μ' z ∧ ν e z = ν' z)
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        EE e j s g = φE e j s g + ∑' ξ : L, φE e j s (adelicWeyl (𝓞 L) L
          * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        NE e j s g = weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) (φE e j s) g))
      (f : AdelicGL2 (𝓞 L) L → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn L f →
      IsBiInvariantUnder L (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) f →
      IsArchBiFinite L tysL f →
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      IntegrableOn (fun x =>
              ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ∑ᶠ q : GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L),
                  ∫ z, ((ξu ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L q.out *
                      (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ∂νZL)
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x)) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' i : ι, convOp L f (b i) x * conj (b i y))
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x)) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) /
                      (((adelicGLHaar (Fin 2) (𝓞 L) L) (AutomorphicForm.canonicalTruncationDomain L α β)).toReal : ℂ) *
                    ∑ᶠ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ |
                          SquaresToXi (𝓞 L) L ⊤ ξu χ ∧
                          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
                            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
                              χ z = 1) ∧
                          Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ)}),
                      (∫ g, f g * chiDet (𝓞 L) L χ g ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) *
                        (chiDet (𝓞 L) L χ x * chiDet (𝓞 L) L χ⁻¹ y))
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x))))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (∀ e : ιE, Integrable (fun t : ℝ => ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv L (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 L) L) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L))
              ∂(maximalCompactHaar L)) *
            (∫ x in Φ₀,
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (EE e i ((t : ℂ) * Complex.I))
                x) *
              conj (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => EE e j ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
                x)
              ∂(adelicGLHaar (Fin 2) (𝓞 L) L)))) ∧
      (Summable fun e : ιE => ∫ t : ℝ, ‖∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv L (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 L) L) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L))
              ∂(maximalCompactHaar L)) *
            (∫ x in Φ₀,
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (EE e i ((t : ℂ) * Complex.I))
                x) *
              conj (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => EE e j ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
                x)
              ∂(adelicGLHaar (Fin 2) (𝓞 L) L))‖) ∧
      (∫ x in Φ₀,
              ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ∑ᶠ q : GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L),
                  ∫ z, ((ξu ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L q.out *
                      (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ∂νZL)
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x)) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' i : ι, convOp L f (b i) x * conj (b i y))
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x)) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) /
                      (((adelicGLHaar (Fin 2) (𝓞 L) L) (AutomorphicForm.canonicalTruncationDomain L α β)).toReal : ℂ) *
                    ∑ᶠ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ |
                          SquaresToXi (𝓞 L) L ⊤ ξu χ ∧
                          (∀ z : (AdeleRing (𝓞 L) L)ˣ,
                            z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
                              χ z = 1) ∧
                          Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ)}),
                      (∫ g, f g * chiDet (𝓞 L) L χ g ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) *
                        (chiDet (𝓞 L) L χ x * chiDet (𝓞 L) L χ⁻¹ y))
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x))) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      (κ : ℂ) * ∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv L (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 L) L) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L))
              ∂(maximalCompactHaar L)) *
            (∫ x in Φ₀,
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (EE e i ((t : ℂ) * Complex.I))
                x) *
              conj (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => EE e j ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
                x)
              ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) := by sorry
