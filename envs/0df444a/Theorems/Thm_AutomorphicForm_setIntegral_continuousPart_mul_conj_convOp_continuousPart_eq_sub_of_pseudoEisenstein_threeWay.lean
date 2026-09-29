-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_continuousPart_mul_conj_convOp_continuousPart_eq_sub_of_pseudoEisenstein_threeWay
-- name    : AutomorphicForm.setIntegral_continuousPart_mul_conj_convOp_continuousPart_eq_sub_of_pseudoEisenstein_threeWay
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/55da1523-036d-5467-91e7-f4c1e9a84058
-- title:
--   Continuous-spectrum part of a pseudo-Eisenstein pairing as a difference
-- statement:
--   Fix a number field $K$ and real numbers $\alpha,\beta$ with $0<\alpha$ and $\alpha<\beta$, and write $\Phi_0 =$ [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) for the canonical truncation domain attached to $(\alpha,\beta)$ (the third component of a classically chosen datum satisfying `IsTruncationDatum K α β`, and $\emptyset$ if no such datum exists). All integrals over $\Phi_0$ are taken with respect to the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` on $\mathrm{GL}_2(\mathbb{A}_K)$ for its Borel structure.
--
--   Throughout, the carrier data are those of `productionPinsOf K Φ₀ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: the Borel $\sigma$-algebra and Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, the domain $\Phi_0$, the full central subgroup $Z=\top\le \mathbb{A}_K^\times$, the level subgroups $M\mapsto \mathrm{principalLevel}(M)\cap \ker(\mathrm{glArch})$, the Hecke generators $v\mapsto \mathrm{heckeGen}(v)$, and, on the adele ring, the Borel $\sigma$-algebra together with the measure $\nu$ obtained by conditioning the additive Haar measure `adelicAddHaar (𝓞 K) K` to the adelic box `adelicBox K` (the box of points whose infinite component lies in the fundamental domain of the lattice basis and whose finite component is everywhere integral).
--
--   Character hypotheses: $\xi_K$ is a monoid homomorphism from $\top\le(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ such that the associated function $z\mapsto \xi_K(z)$ on $(\mathbb{A}_K)^\times$ is continuous ($h\xi c$), is trivial on the image of $K^\times$ under the units map of $K\to\mathbb{A}_K$ ($h\xi t$), and has modulus $1$ at every idele ($h\xi u$).
--
--   Test function: $f:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$, assumed continuous and of compact support. The associated right convolution operator is $\mathrm{convOp}\,K\,f\,u\,(g)=\int u(gx)f(x)\,dx$ against the same Haar measure.
--
--   Profile hypotheses: $\varphi,\psi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ both satisfy [`AutomorphicForm.IsSlabProfile K ⊤ ξK`](def/AutomorphicForm_SlabProfile.html#L17), i.e. each is measurable, invariant under left multiplication by the unipotent matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ for $x\in\mathbb{A}_K$, invariant under left multiplication by the global points of the Borel subgroup (matrices over $K$ with vanishing lower-left entry), transforms under the central scalar $z\cdot I$ by the factor $\xi_K(z)$ for every idele $z$, is bounded on each slab $\{g: \|\det g\|\in[d_1,d_2]\}$ with $d_1>0$, and has support confined to a height band: there are $a,b$ with $0<a$ such that the adelic height `adelicHeight K g` lies in $[a,b]$ whenever the function does not vanish at $g$. Their pseudo-Eisenstein series is $\mathrm{pseudoEisenstein}\,K\,\varphi\,(g)=\varphi(g)+\sum'_{b\in K}\varphi(w\,u(b)\,g)$, with $w$ the adelic Weyl element and $u(b)$ the unipotent matrix with upper-right entry $b$.
--
--   The conclusion is a statement universally quantified over two triples of functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$, $(u_{c,1},u_{r,1},u_{e,1})$ and $(u_{c,2},u_{r,2},u_{e,2})$, each triple subject to the following six hypotheses, stated for $i=1,2$. (i) $u_{c,i}$ satisfies `IsAutomorphicFnAt` for the above pins and $\xi_K$ — the predicate `LsXiMemberAt` for the pins' Borel structure, Haar measure, domain $\Phi_0$, central subgroup $\top$ and character $\xi_K$, referred to here by name. (ii) $u_{c,i}$ is cuspidal almost everywhere: for Haar-almost every $g$, the constant term $\int_{\mathbb{A}_K} u_{c,i}(u(x)g)\,d\nu(x)$, taken with respect to the conditioned measure $\nu$ above, vanishes. (iii) $u_{r,i}$ satisfies `IsAutomorphicFnAt`. (iv) $u_{r,i}$ lies in the $L^2(\Phi_0)$-closure of the automorphic part of the residual span: for every $\varepsilon>0$ there is an $r$ in [`AutomorphicForm.residualSpan (𝓞 K) K ⊤ ξK`](def/AutomorphicForm_ResidualSpan.html#L12) — the $\mathbb{C}$-span of the functions $g\mapsto\chi(\det g)$ for homomorphisms $\chi:(\mathbb{A}_K)^\times\to\mathbb{C}^\times$ with $\chi(z)^2=\xi_K(z)$ for all ideles $z$ — such that $r$ satisfies `IsAutomorphicFnAt` and the $L^2$-norm `eLpNorm (u_{r,i} - r) 2` with respect to Haar measure restricted to $\Phi_0$ is less than `ENNReal.ofReal ε`. (v) $u_{e,i}$ satisfies `IsAutomorphicFnAt`. (vi) $u_{e,i}$ is orthogonal on $\Phi_0$ to every $h$ satisfying `IsAutomorphicFnAt` which is either almost everywhere cuspidal in the sense of (ii) or a member of the residual span: $\int_{\Phi_0} u_{e,i}(g)\overline{h(g)}\,dg = 0$. Finally, the decomposition hypotheses: $\mathrm{pseudoEisenstein}\,K\,\varphi = u_{c,1}+u_{r,1}+u_{e,1}$ and $\mathrm{pseudoEisenstein}\,K\,\psi = u_{c,2}+u_{r,2}+u_{e,2}$, each almost everywhere for Haar measure restricted to $\Phi_0$.
--
--   Under these hypotheses the asserted identity is
--   $$\int_{\Phi_0} u_{e,1}(g)\,\overline{(\mathrm{convOp}\,K\,f\,u_{e,2})(g)}\,dg \;=\; \int_{\Phi_0} (\mathrm{pseudoEisenstein}\,K\,\varphi)(g)\,\overline{(\mathrm{convOp}\,K\,f\,(\mathrm{pseudoEisenstein}\,K\,\psi))(g)}\,dg \;-\; \int_{\Phi_0} u_{r,1}(g)\,\overline{(\mathrm{convOp}\,K\,f\,u_{r,2})(g)}\,dg .$$
--
--   This is the Hilbert-space bookkeeping step that isolates, inside the pairing of two pseudo-Eisenstein series against the right convolution operator $R(f)$ over the truncation domain $\Phi_0$, the contribution of the parts orthogonal to the cuspidal and residual pieces: the cuspidal cross-terms drop out and the residual cross-term is subtracted explicitly. It is used by the statement producing the axis pairing for matched Paley–Wiener data in the continuous-spectrum analysis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_continuousPart_mul_conj_convOp_continuousPart_eq_sub_of_pseudoEisenstein_threeWay.lean

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

theorem AutomorphicForm.setIntegral_continuousPart_mul_conj_convOp_continuousPart_eq_sub_of_pseudoEisenstein_threeWay
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    (φ ψ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hφ : AutomorphicForm.IsSlabProfile K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK φ)
    (_hψ : AutomorphicForm.IsSlabProfile K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ) :
    letI := adeleBorel (𝓞 K) K
    ∀
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
        ue₁ g * conj (convOp K f ue₂ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          AutomorphicForm.pseudoEisenstein K φ g * conj (convOp K f (AutomorphicForm.pseudoEisenstein K ψ) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
      ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          ur₁ g * conj (convOp K f ur₂ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
