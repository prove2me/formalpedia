-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_convOp_continuousProjection_eq_inv_mul_setIntegral_convOp_mul_conj_continuousProjection
-- name    : AutomorphicForm.setIntegral_convOp_continuousProjection_eq_inv_mul_setIntegral_convOp_mul_conj_continuousProjection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/0050942f-92ea-5e39-b211-0ef180210ef9
-- title:
--   Continuous part: integral over A as normalised pairing with u^Aₑ
-- statement:
--   Fix a number field $K$ and real numbers $\alpha,\beta$ with $0<\alpha$ and $\alpha<\beta$. The idele unit group $(\mathbb{A}_K)^\times$ is equipped with a measurable structure which is the Borel structure of its topology, and $\nu_{Z}$ denotes a Haar measure on it; $\Omega_K\subseteq(\mathbb{A}_K)^\times$ is assumed to be a fundamental domain, in the sense of `IsFundamentalDomain`, for the action of the image of $K^\times\to(\mathbb{A}_K)^\times$ (the range of `Units.map` applied to $\operatorname{algebraMap} K\,(\mathbb{A}_K)$) with respect to $\nu_Z$. Further, $\xi_K$ is a monoid homomorphism from the full subgroup $\top\le(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ subject to three conditions: `hξc`, that $z\mapsto\xi_K(z)$ is continuous as a $\mathbb{C}$-valued function; `hξt`, that $\xi_K(z)=1$ for every $z$ in the image of $K^\times$; and `hξu`, that $\lVert\xi_K(z)\rVert=1$ for all $z$. Finally $f:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ is continuous with compact support.
--
--   Throughout, $\Phi_0:=$ [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) is the truncation domain selected by the canonical truncation data for $(\alpha,\beta)$, $\mu:=$ `adelicGLHaar (Fin 2) (𝓞 K) K` is the Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$ for its Borel structure, and $P$ denotes the carrier pins `productionPinsOf K Φ₀ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: that is, the record whose measurable space is the Borel structure on $\mathrm{GL}_2(\mathbb{A}_K)$, whose measure is $\mu$, whose domain is $\Phi_0$, whose central subgroup $Z$ is all of $(\mathbb{A}_K)^\times$, whose level subgroups are $M\mapsto$ `principalLevel (𝓞 K) K M` intersected with the kernel of the archimedean projection `glArch`, whose Hecke generators are the elements `heckeGen (𝓞 K) K v`, and whose adelic measure $\nu$ is the additive adelic Haar measure conditioned on the adelic box `adelicBox K`. For a function $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_K)$, `IsAutomorphicFnAt K P ξ_K φ` is the predicate `LsXiMember` evaluated at the data recorded in $P$ together with the central character $\xi_K$; it is the statement that $\varphi$ lies in the corresponding $L^2$-space of automorphic functions of central character $\xi_K$. The constant term `constantTerm P.ν unipotentGL2 φ g` is $\int \varphi\bigl(\begin{smallmatrix}1&q\\0&1\end{smallmatrix}\bigr)g)\,d\nu(q)$ for $\nu$ the conditioned adelic measure of $P$, and `residualSpan (𝓞 K) K ⊤ ξ_K` is the $\mathbb{C}$-span of the functions $g\mapsto\chi(\det g)$ where $\chi:(\mathbb{A}_K)^\times\to\mathbb{C}^\times$ satisfies $\chi(z)^2=\xi_K(z)$ for all $z$. The operator `convOp K f` sends $u$ to `rightConv K u f`, namely $g\mapsto\int u(gx)f(x)\,d\mu(x)$.
--
--   Under these hypotheses the following holds for all $C,A,B$ and all six functions as follows. Let $C\subseteq\mathrm{GL}_2(\mathbb{A}_K)$ be compact, and let $A,B\subseteq C$ be measurable. Let $u^A_c,u^A_r,u^A_e$ and $u^B_c,u^B_r,u^B_e$ be complex-valued functions on $\mathrm{GL}_2(\mathbb{A}_K)$ satisfying two symmetric groups of hypotheses, one for the superscript $A$ and one for the superscript $B$. For the $A$-group these are: `_hucA`, that $u^A_c$ satisfies `IsAutomorphicFnAt K P ξ_K`; `_huc0A`, that for $\mu$-almost every $g$ the constant term of $u^A_c$ at $g$ vanishes; `_hurA`, that $u^A_r$ satisfies `IsAutomorphicFnAt K P ξ_K`; `_hurcA`, that for every $\varepsilon>0$ there is an element $r$ of `residualSpan (𝓞 K) K ⊤ ξ_K` which itself satisfies `IsAutomorphicFnAt K P ξ_K` and for which the $L^2$-norm `eLpNorm (u^A_r - r) 2` with respect to $\mu$ restricted to $\Phi_0$ is less than $\varepsilon$; `_hueA`, that $u^A_e$ satisfies `IsAutomorphicFnAt K P ξ_K`; `_hueoA`, that for every $h$ satisfying `IsAutomorphicFnAt K P ξ_K` whose constant term vanishes $\mu$-almost everywhere or which lies in `residualSpan (𝓞 K) K ⊤ ξ_K` one has $\int_{\Phi_0} u^A_e(g)\overline{h(g)}\,d\mu(g)=0$; and `_hsumA`, that the function
--   $$g\mapsto \sum^{\mathrm{f}}_{q\in \mathrm{GL}_2(K)/Z(\mathrm{GL}_2(K))}\ \int \xi_K(w)^{-1}\,\bigl(\mathbf 1_{\Phi_0}\cdot\mathbf 1_{A}\bigr)\bigl(z(w)\,\iota(\tilde q)\,g\bigr)\,d\nu_Z(w)$$
--   agrees, almost everywhere with respect to $\mu$ restricted to $\Phi_0$, with $u^A_c+u^A_r+u^A_e$; here the outer sum is the finitely supported sum `∑ᶠ` over the quotient of $\mathrm{GL}_2(K)$ by its centre, $\tilde q$ is the chosen representative `q.out`, $\iota$ is [`AutomorphicForm.globalPoints (𝓞 K) K`](def/AutomorphicForm_AdelicLsXi.html#L15), $z(w)$ is the scalar matrix [`AutomorphicForm.centralScalar (𝓞 K) K w`](def/AutomorphicForm_AdelicLsXi.html#L18), and the integrand's indicator is that of $\Phi_0$ applied to the indicator of $A$ of the constant function $1$. The $B$-group `_hucB`, `_huc0B`, `_hurB`, `_hurcB`, `_hueB`, `_hueoB`, `_hsumB` consists of exactly the same seven conditions with $u^A_\bullet$ replaced by $u^B_\bullet$ and $A$ replaced by $B$.
--
--   The conclusion is the single identity
--   $$\int_{A} \bigl(\mathrm{convOp}\,K\,f\,u^B_e\bigr)(x)\,d\bigl(\mu|_{\Phi_0}\bigr)(x)\;=\;b^{-1}\int_{\Phi_0}\bigl(\mathrm{convOp}\,K\,f\,u^B_e\bigr)(g)\,\overline{u^A_e(g)}\,d\mu(g),$$
--   where the left-hand integral is over the set $A$ with respect to the restriction of $\mu$ to $\Phi_0$, and $b$ is the real number obtained as `.toReal` of
--   $$\nu_Z\Bigl(\Omega_K\cap\{z\mid \mathrm{NumberField.TateGlobal.ideleNorm}\,K\bigl(\det z(z)\bigr)\in[\alpha,\beta]\}\Bigr),$$
--   that is, the $\nu_Z$-measure of the part of the fundamental domain $\Omega_K$ on which the idele norm of the determinant of the scalar matrix $z(z)$ lies in the closed interval $[\alpha,\beta]$, coerced into $\mathbb{C}$ and inverted there.
--
--   This is the first step of the treatment of the continuous (non-cuspidal, non-residual) parts in the adelic truncated-kernel computation for $\mathrm{GL}_2$ over a number field: the integral of $R(f)u^B_e$ over the measurable set $A$ inside the truncation domain is re-expressed as the $L^2$-pairing of $R(f)u^B_e$ against the continuous part $u^A_e$ of the automorphised indicator of $A$, normalised by the central band volume $b$. It is used by [`AutomorphicForm.exists_forall_setIntegral_convOp_continuousProjection_eq_mul_setIntegral_prod_tsum_integral_sum_rightConv_axis_continuation`](thm.html#AutomorphicForm.exists_forall_setIntegral_convOp_continuousProjection_eq_mul_setIntegral_prod_tsum_integral_sum_rightConv_axis_continuation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_convOp_continuousProjection_eq_inv_mul_setIntegral_convOp_mul_conj_continuousProjection.lean

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

theorem AutomorphicForm.setIntegral_convOp_continuousProjection_eq_inv_mul_setIntegral_convOp_mul_conj_continuousProjection
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f) :
    letI := adeleBorel (𝓞 K) K
    ∀ (C : Set (AdelicGL2 (𝓞 K) K)) (_hC : IsCompact C)
      (A : Set (AdelicGL2 (𝓞 K) K)) (_hA : A ⊆ C) (_hAm : MeasurableSet A)
      (B : Set (AdelicGL2 (𝓞 K) K)) (_hB : B ⊆ C) (_hBm : MeasurableSet B)
      (ucA urA ueA : AdelicGL2 (𝓞 K) K → ℂ)
      (_hucA : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ucA) (_huc0A : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 ucA g = 0))
      (_hurA : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK urA)
      (_hurcA : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (urA - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hueA : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ueA)
      (_hueoA : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        ((∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 h g = 0) ∨ h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ueA g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (_hsumA : (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator (A.indicator fun _ => (1 : ℂ))
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] ucA + urA + ueA)
      (ucB urB ueB : AdelicGL2 (𝓞 K) K → ℂ)
      (_hucB : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ucB) (_huc0B : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 ucB g = 0))
      (_hurB : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK urB)
      (_hurcB : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (urB - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hueB : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ueB)
      (_hueoB : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        ((∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 h g = 0) ∨ h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ueB g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (_hsumB : (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator (B.indicator fun _ => (1 : ℂ))
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] ucB + urB + ueB)
,
    ∫ x in A, convOp K f ueB x ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) =
      (((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ))⁻¹ *
      ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        convOp K f ueB g * conj (ueA g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
