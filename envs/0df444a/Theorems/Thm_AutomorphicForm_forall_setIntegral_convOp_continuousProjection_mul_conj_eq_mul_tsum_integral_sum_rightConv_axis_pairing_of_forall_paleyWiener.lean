-- Prove2me | Theorems.Thm_AutomorphicForm_forall_setIntegral_convOp_continuousProjection_mul_conj_eq_mul_tsum_integral_sum_rightConv_axis_pairing_of_forall_paleyWiener
-- name    : AutomorphicForm.forall_setIntegral_convOp_continuousProjection_mul_conj_eq_mul_tsum_integral_sum_rightConv_axis_pairing_of_forall_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/97bcde0a-ae95-52d8-a260-005480cb75f5
-- title:
--   Continuous-spectrum form of R(f) for automorphised bounded cutoffs
-- statement:
--   Throughout, $K$ is a number field, $\alpha,\beta$ are reals with $0<\alpha$ and $\alpha<\beta$, and integration over $\mathrm{GL}_2(\mathbf A_K)$ is with respect to the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K`, restricted where indicated to the truncation region $\Phi_0=$ [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) (the third component of the canonical truncation datum attached to $(\alpha,\beta)$). The following data are fixed: a set $\Phi_K$ of adelic matrices, on which no hypothesis is imposed; reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}<d_{2K}$ and a finite set $T_K\subseteq \mathrm{GL}_2(\mathbf A_K)$ such that `hcovK` holds, i.e. the union $\bigcup_{x\in T_K}(\cdot\,x)\,[\,$`centreCutSiegelSet K cK uK d₁K d₂K`$\,]$ covers $\mathrm{GL}_2(\mathbf A_K)$ modulo left translation by $\mathrm{GL}_2(K)$ and right multiplication by a central idelic scalar; a Haar measure $\nu_{Z,K}$ on the idele units $(\mathbf A_K)^\times$ together with a set $\Omega_K$ which, by `hΩK`, is a fundamental domain for the subgroup of principal ideles (the range of `Units.map` of $K\to\mathbf A_K$) acting on $(\mathbf A_K)^\times$; a finite set $S_K$ of finite places; a homomorphism $\xi_K$ from the full subgroup of $(\mathbf A_K)^\times$ to $\mathbb C^\times$ which is continuous (`hξc`), trivial on principal ideles (`hξt`) and unitary (`hξu`); an ideal $N$ of $\mathcal O_K$ all of whose prime divisors lie in $S_K$ (`hN`); and an archimedean type family $\mathrm{tys}_K$ (a cardinality function on the infinite places together with a choice of that many archimedean representations at each place). The character $\alpha_m\colon(\mathbf A_K)^\times\to\mathbb R^\times$ is the unit-valued homomorphism obtained from the module character `distribHaarChar (AdeleRing (𝓞 K) K)`, and $\alpha_m$ is assumed positive (`hαm`); $\kappa$ is a real number. All automorphy conditions below are taken with respect to the carrier data `productionPinsOf` built from the region $\Phi_0$, the level groups $M\mapsto$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, the Hecke generators `heckeGen`, and the box `adelicBox K`; in particular the ambient central subgroup is all of $(\mathbf A_K)^\times$ and the measure used for constant terms is the adelic additive Haar measure conditioned on `adelicBox K`.
--
--   A cuspidal orthonormal system is fixed: a type $\iota$, functions $b_i\colon\mathrm{GL}_2(\mathbf A_K)\to\mathbb C$ and eigensystems $\mathrm{cls}(i)\in$ `HeckeEigensystem K ℂ`, subject to: `hb`, each $\mathrm{cls}(i)$ lies in `cuspClasses` (level $N$, vanishing $a_v,b_v$ for $v\in S_K$, non-zero isotypic cusp submodule) and $b_i$ lies in the intersection of `isotypicCuspSubmodule` for $\mathrm{cls}(i)$ with `archCutSubmodule K tysK`; `hbn` and `hbo`, the $b_i$ are orthonormal for the pairing $\int_{\Phi_0} b_i\,\overline{b_j}$; `hbs`, for every cusp class $\pi$ the fibre $\{i\mid \mathrm{cls}(i)=\pi\}$ is finite and the $b_i$ over that fibre span the $\pi$-isotypic cusp submodule cut by the archimedean types; and `hbc`, completeness: any $\varphi$ which is a smooth cuspidal automorphic function for $\xi_K$, continuous, invariant under right translation by the level group attached to $N$, in the archimedean cut submodule, and orthogonal on $\Phi_0$ to every $b_i$, vanishes almost everywhere on $\Phi_0$.
--
--   The Eisenstein data consist of: a countable type $\iota_E$; pairs of characters $\mu_e,\nu_e\colon(\mathbf A_K)^\times\to\mathbb C^\times$ which are unitary, trivial on principal ideles, continuous, satisfy $\mu_e\nu_e=\xi_K$, and are pairwise separated already on the norm-one ideles [`NumberField.TateGlobal.normOneIdeles K`](def/NumberField_TateGlobalZeta.html#L16) (hypotheses `_hμ`, `_hν`, `_hμic`, `_hνic`, `_hμc`, `_hνc`, `_hμν`, `_hdist`); integers $n_E(e)$ and section families $\varphi_{E}(e,j,s)$ for $j\in\mathrm{Fin}(n_E(e))$, subject to the group of hypotheses `_hφE`–`_hφEspan` (summarised here): each $\varphi_E(e,j,s)$ is an induced section for the pair $\bigl(\mu_e\,\alpha_m^{\,s+1/2},\ \nu_e\,\alpha_m^{-(s+1/2)}\bigr)$, is archimedean $K$-finite, smooth under the finite-adelic subgroup, jointly continuous in $(s,g)$, entire in $s$ for each $g$, has its right translates under each archimedean row-isometry subgroup inside a fixed finite-dimensional space, is independent of $s$ on the maximal compact subgroup, is right invariant under the level group of $N$, lies in the archimedean cut submodule, is orthonormal in $j$ over the maximal compact subgroup with measure `maximalCompactHaar K`, and spans, for each real $t$, all sections of the same type on the line $s=it$ satisfying the corresponding regularity, level and type conditions; finally `_hpairs` states that every unitary pair $(\mu',\nu')$ of ideleclass characters with $\mu'\nu'=\xi_K$ admitting a non-zero such section on a line $s=it$ agrees with some $(\mu_e,\nu_e)$ on the norm-one ideles. Continuation data are sets $O_E(e,j)\subseteq\mathbb C$ and families $E_E(e,j,s),N_E(e,j,s)$ with `_hEE`: $O_E(e,j)$ is open and preconnected and contains both the imaginary axis and the half-plane $\{\operatorname{Re}s>1/2\}$; for each $g$ the functions $s\mapsto E_E(e,j,s)(g)$ and $s\mapsto N_E(e,j,s)(g)$ are analytic on a neighbourhood of $O_E(e,j)$; both are continuous on $O_E(e,j)\times\mathrm{GL}_2(\mathbf A_K)$; and for $\operatorname{Re}s>1/2$ one has $E_E(e,j,s)(g)=\varphi_E(e,j,s)(g)+\sum_{\xi\in K}\varphi_E(e,j,s)\bigl(w\,u(\xi)\,g\bigr)$ with $w=$ `adelicWeyl` and $u$ the unipotent embedding, while $N_E(e,j,s)=$ `weylIntertwiningIntegral` of $\varphi_E(e,j,s)$ with respect to the adelic additive Haar measure.
--
--   Finally a test function $f\colon\mathrm{GL}_2(\mathbf A_K)\to\mathbb C$ is fixed, continuous and compactly supported, and assumed factorizable (a product of a compactly supported smooth archimedean factor in the matrix entries and a finite-adelic factor), bi-invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, and archimedean bi-finite for $\mathrm{tys}_K$.
--
--   The hypothesis of the implication is the same spectral identity in the Paley–Wiener case: for every finite index type $\iota_P$ with unitary ideleclass character pairs $(\mu_P,\nu_P)$ which are continuous, satisfy $\mu_P(z)\nu_P(z)=\xi_K(z)$ on the central subgroup, are permuted by a swap map $r_P$ interchanging $\mu_P$ and $\nu_P$, and are pairwise separated on the norm-one ideles; for all section families $\varphi_f,\psi_f$ which are induced sections for $\bigl(\mu_P(e)\alpha_m^{s+1/2},\nu_P(e)\alpha_m^{-(s+1/2)}\bigr)$, jointly continuous, entire in $s$, with $\psi_f$ archimedean $K$-finite, smooth and of uniformly finite $K$-type, and with both families satisfying rapid decay along vertical strips (for every $n$, every $\sigma_0$ and every compact $C$ there is an integrable bounded majorant $m$ with $(1+|t|)^n\|\varphi_f(e,\sigma'+it)(g)\|\le m(t)$ for $|\sigma'|\le\sigma_0$, $g\in C$, and likewise for $\psi_f$); for all $\varphi,\psi$ which are slab profiles for $\xi_K$ (measurable, invariant under left unipotent and rational Borel translation, transforming by $\xi_K$ under the centre, bounded on determinant slabs, with height support in a band) represented on every vertical line by $\varphi(g)=\sum_{e}(4\pi)^{-1}\int_{\mathbb R}\varphi_f(e,\sigma'+it)(g)\,dt$ and similarly for $\psi$; for a matching $(\mathrm{em},\tau)$ with $\mu_P(i)=\mu_{\mathrm{em}(i)}\cdot\|\cdot\|^{i\tau(i)}$ and $\nu_P(i)=\nu_{\mathrm{em}(i)}\cdot\|\cdot\|^{-i\tau(i)}$ (hypothesis `_hem`, using [`NumberField.TateGlobal.normPowChar`](def/NumberField_NormPowChar.html#L22)); and for all spectral decompositions of the two pseudo-Eisenstein series, that is triples $(u_{c,m},u_{r,m},u_{e,m})$, $m=1,2$, of automorphic functions for $\xi_K$ such that $u_{c,m}$ has almost everywhere vanishing constant term along the unipotent, $u_{r,m}$ is approximable in $L^2(\Phi_0)$ to arbitrary accuracy by automorphic elements of [`AutomorphicForm.residualSpan`](def/AutomorphicForm_ResidualSpan.html#L12) (the span of the functions $\chi\circ\det$ with $\chi^2=\xi_K$ on the centre), $u_{e,m}$ is orthogonal on $\Phi_0$ to every automorphic $h$ whose constant term vanishes almost everywhere or which lies in the residual span, and $u_{c,1}+u_{r,1}+u_{e,1}$ agrees almost everywhere on $\Phi_0$ with [`AutomorphicForm.pseudoEisenstein K φ`](def/AutomorphicForm_SlabProfile.html#L32) while $u_{c,2}+u_{r,2}+u_{e,2}$ agrees almost everywhere with [`AutomorphicForm.pseudoEisenstein K ψ`](def/AutomorphicForm_SlabProfile.html#L32) — under all of this, $$\int_{\Phi_0}\bigl(\mathrm{convOp}_f u_{e,2}\bigr)(g)\,\overline{u_{e,1}(g)}\,d\mu=\kappa\sum_{e\in\iota_E}\int_{\mathbb R}\sum_{i,j}a_{e,ij}(t)\,\Theta_\psi(e,j,t)\,\overline{\Theta_\varphi(e,i,t)}\,dt,$$ where $\mathrm{convOp}_f u=$ `rightConv K u f`, i.e. $g\mapsto\int u(gx)f(x)\,dx$, $a_{e,ij}(t)=\int_{\mathbf K}$ `rightConv K (φE e j (it)) f` $(k)\,\overline{\varphi_E(e,i,it)(k)}\,d$ `maximalCompactHaar K`, and $\Theta_\psi(e,j,t)=\int_{\Phi_0}$ `pseudoEisenstein K ψ` $(g)\,\overline{E_E(e,j,it)(g)}\,d\mu$, $\Theta_\varphi(e,i,t)$ likewise with $\varphi$; the sum over $\iota_E$ is an unconditional sum.
--
--   The conclusion asserts the same identity for automorphisations of bounded compactly supported cutoffs. Namely, for all measurable $\Psi_1,\Psi_2\colon\mathrm{GL}_2(\mathbf A_K)\to\mathbb C$ each vanishing off some compact set and bounded in norm, and for all triples $(u_{c,m},u_{r,m},u_{e,m})$, $m=1,2$, of automorphic functions for $\xi_K$ satisfying exactly the same four conditions as above — $u_{c,m}$ automorphic with almost everywhere vanishing unipotent constant term, $u_{r,m}$ automorphic and $L^2(\Phi_0)$-approximable by automorphic elements of the residual span, $u_{e,m}$ automorphic and orthogonal on $\Phi_0$ to every automorphic function that either has almost everywhere vanishing constant term or lies in the residual span — but now with the summation hypotheses requiring that $u_{c,m}+u_{r,m}+u_{e,m}$ agree almost everywhere on $\Phi_0$ with the automorphisation $$\Theta_m(g)=\sum_{q\in\mathrm{GL}_2(K)/Z}\ \int_{(\mathbf A_K)^\times}\xi_K(w)^{-1}\,\bigl(\mathbf 1_{\Phi_0}\Psi_m\bigr)\bigl(z(w)\cdot(\gamma(q.\mathrm{out})\,g)\bigr)\,d\nu_{Z,K}(w)$$ (a finite sum over the coset space of $\mathrm{GL}_2(K)$ by its centre, with $z$ the central scalar embedding [`AutomorphicForm.centralScalar`](def/AutomorphicForm_AdelicLsXi.html#L18) and $\gamma$ the global-points embedding [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15) evaluated at a chosen representative of the coset), one has $$\int_{\Phi_0}\bigl(\mathrm{convOp}_f u_{e,2}\bigr)(g)\,\overline{u_{e,1}(g)}\,d\mu=\kappa\sum_{e\in\iota_E}\int_{\mathbb R}\sum_{i,j\in\mathrm{Fin}(n_E(e))}a_{e,ij}(t)\cdot\Bigl(\int_{\Phi_0}\Theta_2(g)\,\overline{E_E(e,j,it)(g)}\,d\mu\Bigr)\cdot\overline{\Bigl(\int_{\Phi_0}\Theta_1(g)\,\overline{E_E(e,i,it)(g)}\,d\mu\Bigr)}\,dt,$$ with $a_{e,ij}(t)$ the same local matrix coefficient over the maximal compact subgroup as above.
--
--   This is the extension-by-density step on the continuous-spectrum side of the Arthur–Selberg trace formula for $\mathrm{GL}_2$ over a number field: the spectral identity for the $\mathbb E$-component of $R(f)$, known for pseudo-Eisenstein series built from Paley–Wiener families of sections, is transported to the pairings arising from automorphised bounded compactly supported cutoffs. It feeds the existence statement [`AutomorphicForm.exists_forall_setIntegral_convOp_continuousProjection_mul_conj_continuousProjection_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_mul_conj_axis_continuation`](thm.html#AutomorphicForm.exists_forall_setIntegral_convOp_continuousProjection_mul_conj_continuousProjection_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_mul_conj_axis_continuation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_forall_setIntegral_convOp_continuousProjection_mul_conj_eq_mul_tsum_integral_sum_rightConv_axis_pairing_of_forall_paleyWiener.lean

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

theorem AutomorphicForm.forall_setIntegral_convOp_continuousProjection_mul_conj_eq_mul_tsum_integral_sum_rightConv_axis_pairing_of_forall_paleyWiener
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
    ∀ (κ : ℝ),
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
    (∀
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
      (φf ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (φf e s))
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hφjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φf e p.1 p.2))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hφhol : ∀ e g, Differentiable ℂ (fun s => φf e s g))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite K (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth K (ψf e s))
      (_hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hφdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (φ ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK φ)
      (_hψ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ)
      (_hφrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        φ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (em : ιP → ιE) (τ : ιP → ℝ)
      (_hem : ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹)
      (uc₁ ur₁ ue₁ : AdelicGL2 (𝓞 K) K → ℂ)
      (_huc₁ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK uc₁) (_huc0₁ : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 uc₁ g = 0))
      (_hur₁ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ur₁)
      (_hurc₁ : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (ur₁ - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hue₁ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ue₁)
      (_hueo₁ : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        ((∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 h g = 0) ∨ h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ue₁ g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (_hsum₁ : AutomorphicForm.pseudoEisenstein K φ =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] uc₁ + ur₁ + ue₁)
      (uc₂ ur₂ ue₂ : AdelicGL2 (𝓞 K) K → ℂ)
      (_huc₂ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK uc₂) (_huc0₂ : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 uc₂ g = 0))
      (_hur₂ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ur₂)
      (_hurc₂ : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (ur₂ - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hue₂ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ue₂)
      (_hueo₂ : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        ((∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 h g = 0) ∨ h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ue₂ g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (_hsum₂ : AutomorphicForm.pseudoEisenstein K ψ =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] uc₂ + ur₂ + ue₂),
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        convOp K f ue₂ g * conj (ue₁ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (κ : ℂ) * ∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            ((∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
                AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
              conj (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
                AutomorphicForm.pseudoEisenstein K φ g * conj (EE e i ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)))) →
    ∀
      (Ψ₁ : AdelicGL2 (𝓞 K) K → ℂ) (_hΨ₁m : Measurable Ψ₁)
      (_hΨ₁c : ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧ ∀ y ∉ C, Ψ₁ y = 0)
      (_hΨ₁b : ∃ M : ℝ, ∀ y, ‖Ψ₁ y‖ ≤ M)
      (Ψ₂ : AdelicGL2 (𝓞 K) K → ℂ) (_hΨ₂m : Measurable Ψ₂)
      (_hΨ₂c : ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧ ∀ y ∉ C, Ψ₂ y = 0)
      (_hΨ₂b : ∃ M : ℝ, ∀ y, ‖Ψ₂ y‖ ≤ M)
      (uc₁ ur₁ ue₁ : AdelicGL2 (𝓞 K) K → ℂ)
      (_huc₁ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK uc₁) (_huc0₁ : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 uc₁ g = 0))
      (_hur₁ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ur₁)
      (_hurc₁ : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (ur₁ - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hue₁ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ue₁)
      (_hueo₁ : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        ((∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 h g = 0) ∨ h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ue₁ g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (_hsum₁ : (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ₁
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] uc₁ + ur₁ + ue₁)
      (uc₂ ur₂ ue₂ : AdelicGL2 (𝓞 K) K → ℂ)
      (_huc₂ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK uc₂) (_huc0₂ : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 uc₂ g = 0))
      (_hur₂ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ur₂)
      (_hurc₂ : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (ur₂ - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hue₂ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ue₂)
      (_hueo₂ : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        ((∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 h g = 0) ∨ h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ue₂ g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (_hsum₂ : (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ₂
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] uc₂ + ur₂ + ue₂),
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        convOp K f ue₂ g * conj (ue₁ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (κ : ℂ) * ∑' e : ιE, ∫ t : ℝ, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv K (φE e j ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
            ((∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
                (fun g : AdelicGL2 (𝓞 K) K =>
              ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
                  (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ₂
                    (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
              conj (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
                (fun g : AdelicGL2 (𝓞 K) K =>
              ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
                  (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ₁
                    (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE e i ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) := by sorry
