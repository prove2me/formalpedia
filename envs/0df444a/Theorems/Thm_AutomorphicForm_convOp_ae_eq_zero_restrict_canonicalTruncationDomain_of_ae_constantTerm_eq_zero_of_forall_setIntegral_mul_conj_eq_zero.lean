-- Prove2me | Theorems.Thm_AutomorphicForm_convOp_ae_eq_zero_restrict_canonicalTruncationDomain_of_ae_constantTerm_eq_zero_of_forall_setIntegral_mul_conj_eq_zero
-- name    : AutomorphicForm.convOp_ae_eq_zero_restrict_canonicalTruncationDomain_of_ae_constantTerm_eq_zero_of_forall_setIntegral_mul_conj_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/5aa2f140-5c8b-5bcf-a562-9d7d3d4adc8e
-- title:
--   Hecke translate of an orthogonal cuspidal remainder vanishes
-- statement:
--   Let $K$ be a number field and $\alpha,\beta$ reals with $0<\alpha<\beta$; write $\Phi_0 =$ [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) for the canonical truncation domain and $\mu =$ `adelicGLHaar (Fin 2) (𝓞 K) K` for the Haar measure on $GL_2(\mathbb A_K)$ attached to its Borel structure. Given are: a set $\Phi_K$ of adelic matrices (no hypothesis is imposed on it); reals $c_K,u_K,d_{1K},d_{2K}$ with $c_K>0$, $0<d_{1K}<d_{2K}$ and a finite set $T_K$ of adelic matrices such that the union of the right translates $(\cdot\, x)''\,$`centreCutSiegelSet K cK uK d₁K d₂K` over $x\in T_K$ covers $GL_2(\mathbb A_K)$ modulo the centre, i.e. for every $g$ there are $\gamma\in GL_2(K)$ and an idele unit $z$ with $\gamma g z$ in that union; a Haar measure $\nu_{Z,K}$ on $\mathbb A_K^\times$ together with a set $\Omega_K$ which is a fundamental domain for the image of $K^\times$ in $\mathbb A_K^\times$; a finite set $S_K$ of finite places; a character $\xi_K$ of the full subgroup of $\mathbb A_K^\times$ into $\mathbb C^\times$ which is continuous, unitary ($|\xi_K(z)|=1$ for all $z$) and trivial on the image of $K^\times$; an ideal $N$ of $\mathcal O_K$ all of whose prime divisors lie in $S_K$; and a family `tysK` of archimedean types, consisting of a number of representations of the row-isometry subgroup at each infinite place. Throughout, `pins` denotes the carrier data `productionPinsOf` built from $\Phi_0$, the congruence subgroups $M \mapsto$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, the Hecke generators `heckeGen (𝓞 K) K v` and the adelic box, with $\mu$ as the measure on $GL_2(\mathbb A_K)$, $Z=\top$ and, on the adele ring, the additive Haar measure conditioned on the adelic box. The assertion is: for every index type $\iota$, every family $b : \iota \to (GL_2(\mathbb A_K)\to\mathbb C)$ and every assignment $\mathrm{cls} : \iota \to$ `HeckeEigensystem K ℂ` such that (i) each $\mathrm{cls}\,i$ lies in `cuspClasses K pins ξK N SK` and each $b_i$ lies in `isotypicCuspSubmodule K pins ξK N SK (cls i)` intersected with `archCutSubmodule K tysK`, (ii) for each cusp class $\pi$ the set $\{i \mid \mathrm{cls}\,i = \pi\}$ is finite and the $\mathbb C$-span of the corresponding $b_i$ is exactly that isotypic cusp submodule cut by the archimedean types, and (iii) the family is complete in the sense that any $\varphi$ which is a smooth cuspidal automorphic function at `pins` for $\xi_K$, is continuous, is right invariant under `pins.U N`, lies in `archCutSubmodule K tysK` and satisfies $\int_{\Phi_0}\varphi\,\overline{b_i}\,d\mu = 0$ for all $i$, vanishes $\mu$-almost everywhere on $\Phi_0$; and for every continuous, compactly supported $f$ which is factorizable (a product of a smooth compactly supported archimedean factor and a locally constant compactly supported finite factor), bi-invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, and `IsArchBiFinite K tysK`; the following holds: for every $w$ which is automorphic at `pins` for $\xi_K$, whose constant term along the unipotent subgroup with respect to `pins.ν` vanishes for $\mu$-almost every $g$, and which satisfies $\int_{\Phi_0} w\,\overline{b_i}\,d\mu = 0$ for all $i$, the right convolution `convOp K f w`, namely $g \mapsto \int w(gx) f(x)\,d\mu(x)$, is zero almost everywhere for $\mu$ restricted to $\Phi_0$.
--
--   This is the remainder step in the cuspidal block of the $L^2$ spectral expansion of the automorphic kernel: a Hecke operator of level $N$ and prescribed archimedean types annihilates, on the truncation domain, any almost-everywhere cuspidal automorphic function orthogonal to the chosen system of isotypic cusp forms. It feeds the expansion [`AutomorphicForm.hasSum_setIntegral_mul_conj_mul_setIntegral_convOp_of_orthonormal_isotypicCuspSubmodule`](thm.html#AutomorphicForm.hasSum_setIntegral_mul_conj_mul_setIntegral_convOp_of_orthonormal_isotypicCuspSubmodule). No orthonormality of the family $(b_i)$ is assumed, only the spanning and completeness conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_convOp_ae_eq_zero_restrict_canonicalTruncationDomain_of_ae_constantTerm_eq_zero_of_forall_setIntegral_mul_conj_eq_zero.lean

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

theorem AutomorphicForm.convOp_ae_eq_zero_restrict_canonicalTruncationDomain_of_ae_constantTerm_eq_zero_of_forall_setIntegral_mul_conj_eq_zero
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
    letI := adeleBorel (𝓞 K) K
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
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
    ∀ (w : AdelicGL2 (𝓞 K) K → ℂ)
      (_hw : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK w) (_hw0 : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 w g = 0))
      (_hwo : ∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, w g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0),
    convOp K f w =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] 0 := by sorry
