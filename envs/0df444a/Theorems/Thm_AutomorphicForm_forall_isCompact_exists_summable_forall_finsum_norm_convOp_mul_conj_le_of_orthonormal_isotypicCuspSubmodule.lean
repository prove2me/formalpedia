-- Prove2me | Theorems.Thm_AutomorphicForm_forall_isCompact_exists_summable_forall_finsum_norm_convOp_mul_conj_le_of_orthonormal_isotypicCuspSubmodule
-- name    : AutomorphicForm.forall_isCompact_exists_summable_forall_finsum_norm_convOp_mul_conj_le_of_orthonormal_isotypicCuspSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/eecbb7d6-68e1-5fe9-bee9-e541b6749caf
-- title:
--   Class-block summable majorant for the cuspidal kernel
-- statement:
--   Let $K$ be a number field and $0<\alpha<\beta$ reals. Fix a set $\Phi_K$ of adelic matrices (on which no hypothesis is imposed), reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}<d_{2K}$ and a finite set $T_K\subseteq GL_2(\mathbb{A}_K)$ such that $\bigcup_{x\in T_K}(\cdot\,x)''\,\mathrm{centreCutSiegelSet}\,K\,c_K u_K d_{1K} d_{2K}$ covers $GL_2(\mathbb{A}_K)$ modulo $GL_2(K)$ on the left and the centre on the right; a Haar measure $\nu_{ZK}$ on $\mathbb{A}_K^\times$ with a fundamental domain $\Omega_K$ for the subgroup of principal ideles; a finite set $S_K$ of finite places; a continuous character $\xi_K$ of $\mathbb{A}_K^\times$ (as the top subgroup) with values in $\mathbb{C}^\times$, trivial on principal ideles and of absolute value $1$; an ideal $N$ all of whose prime divisors lie in $S_K$; and an archimedean type family $\mathrm{tys}_K$. Write $\mathrm{pins}$ for the carrier data with domain the canonical truncation domain of $(\alpha,\beta)$, Haar measure $\mathrm{adelicGLHaar}$, central subgroup $\top$, level subgroups $M\mapsto \mathrm{principalLevel}\,N\sqcap\mathrm{finiteAdelicGL2Subgroup}$, Hecke generators $\mathrm{heckeGen}\,v$ and the adelic box conditioning on $\mathbb{A}_K$. Assume the positivity of the real character $\alpha_m$ built from $\mathrm{distribHaarChar}(\mathbb{A}_K)$. Let $\iota$ be a type, $b:\iota\to (GL_2(\mathbb{A}_K)\to\mathbb{C})$ and $\mathrm{cls}:\iota\to$ Hecke eigensystems over $\mathbb{C}$, subject to: each $\mathrm{cls}\,i$ is a cusp class for $(\mathrm{pins},\xi_K,N,S_K)$ and $b\,i$ lies in the isotypic cusp submodule of $\mathrm{cls}\,i$ intersected with the archimedean cut submodule of $\mathrm{tys}_K$; the $b\,i$ are orthonormal for the inner product $\int_{\,\mathrm{canonicalTruncationDomain}} b\,i\cdot\overline{b\,j}$ against $\mathrm{adelicGLHaar}$; each class fibre $\{i\mid \mathrm{cls}\,i=\pi\}$ is finite and $b$ spans that cut isotypic space; and the system is complete, in the sense that any continuous smooth cuspidal automorphic function for $(\mathrm{pins},\xi_K)$ which is right invariant under $\mathrm{principalLevel}\,N\sqcap\mathrm{finiteAdelicGL2Subgroup}$, lies in the archimedean cut submodule and is orthogonal to every $b\,i$ vanishes almost everywhere on the truncation domain. Finally let $f:GL_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous with compact support, factorizable as a smooth compactly supported archimedean factor times a locally constant compactly supported finite factor, bi-invariant under $\mathrm{principalLevel}\,N\sqcap\mathrm{finiteAdelicGL2Subgroup}$, and archimedean bi-finite for $\mathrm{tys}_K$. Then for every compact $C\subseteq GL_2(\mathbb{A}_K)$ there is a summable function $M$ on Hecke eigensystems such that for every eigensystem $\pi$ and all $x,y\in C$, $\sum_{i:\ \mathrm{cls}\,i=\pi}\bigl\|\,(\mathrm{convOp}\,f\,(b\,i))(x)\cdot\overline{b\,i(y)}\,\bigr\|\le M(\pi)$, where $(\mathrm{convOp}\,f\,u)(g)=\int u(gx)f(x)\,dx$.
--
--   This is the Weierstrass majorant needed for the cuspidal kernel $\sum_i (R(f)b_i)(x)\overline{b_i(y)}$ of an adelic test function, organised by cuspidal class: each class block is a finite sum, and the blocks are dominated on compacta by a summable family indexed by Hecke eigensystems. It feeds the joint continuity of the kernel on compact sets and the identification of the integral of $\mathrm{convOp}$ applied to the cuspidal projection with an integral of the kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_forall_isCompact_exists_summable_forall_finsum_norm_convOp_mul_conj_le_of_orthonormal_isotypicCuspSubmodule.lean

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

theorem AutomorphicForm.forall_isCompact_exists_summable_forall_finsum_norm_convOp_mul_conj_le_of_orthonormal_isotypicCuspSubmodule
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
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
    ∀ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C →
      ∃ M : HeckeEigensystem K ℂ → ℝ, Summable M ∧
        ∀ (π : HeckeEigensystem K ℂ), ∀ x ∈ C, ∀ y ∈ C,
          ∑ᶠ i : {i // cls i = π}, ‖convOp K f (b i) x * conj (b i y)‖ ≤ M π := by sorry
