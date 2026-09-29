-- Prove2me | Theorems.Thm_AutomorphicForm_hasSum_setIntegral_mul_conj_mul_setIntegral_convOp_of_orthonormal_isotypicCuspSubmodule
-- name    : AutomorphicForm.hasSum_setIntegral_mul_conj_mul_setIntegral_convOp_of_orthonormal_isotypicCuspSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/779b1f26-4bd5-54c5-94a3-5ddb8fdb663d
-- title:
--   Expansion of int_A R(f)u along an orthonormal cusp system
-- statement:
--   Let $K$ be a number field, let $0<\alpha<\beta$, let $\Phi_K$ be a set of elements of $\mathrm{GL}_2(\mathbb{A}_K)$, and let $c_K,u_K,d_{1K},d_{2K}$ be reals with $c_K>0$, $0<d_{1K}<d_{2K}$ and $T_K$ a finite set of adelic matrices such that the union of the right translates by $x\in T_K$ of the centre-cut Siegel set (those $g$ whose finite part is integral, with $c_K\le$ local height and $x$-window square $\le u_K^2$ at every infinite place, and archimedean determinant norm in $[d_{1K},d_{2K}]$ at every infinite place) covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo $\mathrm{GL}_2(K)$ and the centre. Let $\nu_{ZK}$ be a Haar measure on $\mathbb{A}_K^\times$ with $\Omega_K$ a fundamental domain for the image of $K^\times$, let $S_K$ be a finite set of finite places, let $\xi_K$ be a homomorphism from the full unit group to $\mathbb{C}^\times$ which is continuous, unitary and trivial on $K^\times$, let $N$ be an ideal all of whose prime divisors lie in $S_K$, and let $\mathrm{tys}_K$ be a family of archimedean types (for each infinite place $w$, a finite list of representations of the row-isometry subgroup at $w$). Throughout, the carrier data are the production pins built from the canonical truncation domain $\Phi_0=\,$`canonicalTruncationDomain K α β`, the level subgroups $M\mapsto$ principal level $M$ intersected with the finite adelic subgroup, the Hecke generators $\mathrm{heckeGen}_v$, and the adelic box, so that the measure on $\mathrm{GL}_2(\mathbb{A}_K)$ is the Haar measure $\mu=\,$`adelicGLHaar`, the central subgroup is all of $\mathbb{A}_K^\times$, and the measure used for constant terms is the Haar measure of $\mathbb{A}_K$ conditioned on the adelic box. The assertion is: for every index type $\iota$, every family $b:\iota\to(\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ and every assignment $\mathrm{cls}:\iota\to$ Hecke eigensystems over $\mathbb{C}$ such that (i) each $\mathrm{cls}\,i$ is a cuspidal class of level $N$ (eigenvalues $a_v=b_v=0$ for $v\in S_K$, non-zero isotypic cusp submodule) and $b_i$ lies in the isotypic cusp submodule of $\mathrm{cls}\,i$ intersected with the archimedean cut submodule of $\mathrm{tys}_K$, (ii) $\int_{\Phi_0} b_i\overline{b_i}\,d\mu=1$ and $\int_{\Phi_0} b_i\overline{b_j}\,d\mu=0$ for $i\ne j$, (iii) for every cuspidal class $\pi$ the set $\{i:\mathrm{cls}\,i=\pi\}$ is finite and the $\mathbb{C}$-span of the corresponding $b_i$ is exactly the isotypic cusp submodule of $\pi$ cut by the types, and (iv) every continuous, $K_f$-smooth cusp automorphic function $\varphi$ for $\xi_K$ which is right invariant under the level-$N$ subgroup, lies in the archimedean cut submodule and satisfies $\int_{\Phi_0}\varphi\overline{b_i}\,d\mu=0$ for all $i$, vanishes $\mu$-almost everywhere on $\Phi_0$; and for every continuous, compactly supported test function $f$ which is factorizable (a product of a smooth compactly supported archimedean factor and a locally constant compactly supported finite factor), bi-invariant under the principal level-$N$ subgroup intersected with the finite adelic subgroup, and archimedean bi-finite for $\mathrm{tys}_K$; and for every measurable $A\subseteq\mathrm{GL}_2(\mathbb{A}_K)$ and every $u$ which is automorphic for $\xi_K$ in the sense of the pins and whose unipotent constant term $g\mapsto\int u(n(x)g)\,d\nu(x)$ vanishes for almost every $g$: the family $$i\mapsto\Big(\int_{\Phi_0}u\,\overline{b_i}\,d\mu\Big)\int_A (R(f)b_i)\,d(\mu|_{\Phi_0})$$ has sum $\int_A (R(f)u)\,d(\mu|_{\Phi_0})$, where $(R(f)\varphi)(g)=\int \varphi(gx)f(x)\,d\mu(x)$.
--
--   This is the projection step for the cuspidal block of the $L^2$ spectral expansion of the automorphic kernel: the integral of $R(f)u$ over a measurable set is expanded unconditionally along a complete orthonormal system of cusp forms of fixed level and archimedean types, the statement being recorded as a `HasSum` so that summability and value come together. It is used by [`AutomorphicForm.setIntegral_convOp_cuspProjection_eq_mul_setIntegral_prod_tsum_convOp_mul_conj_of_orthonormal_isotypicCuspSubmodule`](thm.html#AutomorphicForm.setIntegral_convOp_cuspProjection_eq_mul_setIntegral_prod_tsum_convOp_mul_conj_of_orthonormal_isotypicCuspSubmodule), where it is combined with the coefficient formula for $\int_{\Phi_0}u\overline{b_i}$ and a sum–integral interchange.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_hasSum_setIntegral_mul_conj_mul_setIntegral_convOp_of_orthonormal_isotypicCuspSubmodule.lean

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

theorem AutomorphicForm.hasSum_setIntegral_mul_conj_mul_setIntegral_convOp_of_orthonormal_isotypicCuspSubmodule
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
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
    ∀ (A : Set (AdelicGL2 (𝓞 K) K)) (_hAm : MeasurableSet A)
      (u : AdelicGL2 (𝓞 K) K → ℂ)
      (_hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u) (_hu0 : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 u g = 0)),
    HasSum (fun i : ι => (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, u g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
        ∫ x in A, convOp K f (b i) x ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)))
      (∫ x in A, convOp K f u x ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))) := by sorry
