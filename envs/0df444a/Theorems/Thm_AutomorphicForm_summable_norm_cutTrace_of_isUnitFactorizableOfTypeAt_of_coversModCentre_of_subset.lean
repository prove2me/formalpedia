-- Prove2me | Theorems.Thm_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset
-- name    : AutomorphicForm.summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/d6f239e4-af65-573e-815c-89cca13b8cd5
-- title:
--   Absolute summability of cut traces over Siegel-pinned cusp classes
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $c>0$, $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$ such that the set $D=\bigcup_{x\in T}\{gx: g\in \mathfrak S\}$, where $\mathfrak S=$ `centreCutSiegelSet K c u d₁ d₂` consists of those $g$ whose finite part lies in $\mathrm{GL}_2(\widehat{\mathcal O}_K)$ and whose archimedean component satisfies, at every infinite place $w$, $c\le$ `localHeight`, `xWindowSq` $\le u^2$ and `archDetNorm` $w\,g\in[d_1,d_2]$, covers modulo the centre: every $g\in\mathrm{GL}_2(\mathbb{A}_K)$ admits $\gamma\in\mathrm{GL}_2(K)$ and $z\in\mathbb{A}_K^\times$ with $\gamma g z\in D$. Let $0<\alpha<\beta$ and let $\Phi$ be contained in the slab $\{\,\| \det g\|_{\mathbb{A}}\in[\alpha,\beta]\}$ and be a fundamental domain for the image of $\mathrm{GL}_2(K)$ acting on the adelic Haar measure of $\mathrm{GL}_2(\mathbb{A}_K)$ restricted to that slab. Let $S$ be a finite set of finite places, $\xi$ a homomorphism from the full idele unit group to $\mathbb{C}^\times$, $N'$ an ideal all of whose prime divisors lie in $S$, and assume for each $w\notin S$ that $(\mathrm{heckeGen}\, w)^{-1}=z\,u_1\,(\mathrm{heckeGen}\, w)\,u_2$ for some central idele scalar $z$ and some $u_1,u_2$ in $U=$ `principalLevel` $N'\sqcap$ `finiteAdelicGL2Subgroup`. Let `tys` be an archimedean type family, $f$ a continuous compactly supported function on $\mathrm{GL}_2(\mathbb{A}_K)$, and $S'\supseteq S$ a finite set of places such that $f$ is unit-factorizable at $S'$ for the level $U$ (bi-$U$-invariant and a product of an archimedean test factor with a finite factor given by local test functions at the places of $S'$ and supported on the integral set outside $S'$) and archimedean bi-finite for `tys`. Then the family, indexed by the Hecke eigensystems $\pi$ with level $N'$, vanishing coefficients $a_v=b_v=0$ for $v\in S$ and nonzero isotypic cusp submodule relative to the carrier pins `productionPinsOf` built from $D$, the levels $U$, the Hecke generators and the adelic box, of the absolute values of the cut traces of right convolution by $f$ on the intersection of the $\pi$-isotypic cusp submodule with the archimedean cut submodule, is summable.
--
--   This is the spectral-side finiteness input for the trace-formula comparison: the absolute convergence of the sum over cuspidal Hecke eigensystems, pinned by a Siegel covering datum and a slab fundamental domain, of the traces of right convolution by a factorizable test function. It is used in the comparison of Hecke-word sums of twisted and untwisted cut traces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_DedekindDomain_IntegralClosure
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain MeasureTheory NumberField.AdelicHaar NumberField.TateGlobal AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering LocalGL2
open AutomorphicForm
open scoped TensorProduct Pointwise TensorProduct.RightActions ComplexConjugate BigOperators NumberField NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset
    (K : Type) [Field K] [NumberField K]
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (hΦKs : ΦK ⊆
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦK : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range ΦK
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (N' : Ideal (𝓞 K)) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (hstd : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ SK →
      ∃ (z : (AdeleRing (𝓞 K) K)ˣ) (u₁ u₂ : AdelicGL2 (𝓞 K) K),
        u₁ ∈ principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K ∧
        u₂ ∈ principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K ∧
        (heckeGen (𝓞 K) K w)⁻¹ = centralScalar (𝓞 K) K z * u₁ * heckeGen (𝓞 K) K w * u₂)
    (tysK : ArchTypeFamily K) (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f)
    (S' : Finset (HeightOneSpectrum (𝓞 K))) (hS' : SK ⊆ S')
    (hft : IsUnitFactorizableOfTypeAt K tysK (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) S' f) :
    Summable (fun π : ↥(cuspClasses K
        (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N' SK) =>
      ‖cutTrace K
          (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N' SK π tysK f hf hfc‖) := by sorry
