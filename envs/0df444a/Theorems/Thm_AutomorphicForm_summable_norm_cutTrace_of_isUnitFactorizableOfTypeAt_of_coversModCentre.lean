-- Prove2me | Theorems.Thm_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre
-- name    : AutomorphicForm.summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/88df2cc8-917e-50cb-8b04-4e906901e854
-- title:
--   Absolute summability of Siegel-pinned cut traces on GL₂
-- statement:
--   Let $K$ be a number field, let $c_K,u_K,d_{1K},d_{2K}$ be reals with $c_K>0$, $0<d_{1K}<d_{2K}$, and let $T_K$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$ such that the union $D=\bigcup_{x\in T_K}(\,\cdot\,x)\big(\mathrm{centreCutSiegelSet}\,K\,c_K\,u_K\,d_{1K}\,d_{2K}\big)$ of right translates of the windowed Siegel set (those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at every infinite place has local height $\ge c_K$ and window coordinate $\mathrm{xWindowSq}\le u_K^2$, and with $\mathrm{archDetNorm}_w(g)\in[d_{1K},d_{2K}]$ for all $w$) satisfies `CoversModCentre`: every $g$ admits $\gamma\in\mathrm{GL}_2(K)$ and $z\in\mathbb{A}_K^\times$ with $\gamma g z\in D$. Let $0<\alpha<\beta$ and let $\Phi_K$ be a subset of the slab $\{g:\ \|\det g\|_{\mathbb{A}_K}\in[\alpha,\beta]\}$ which is a fundamental domain for the image of $\mathrm{GL}_2(K)$ acting on the adelic Haar measure of $\mathrm{GL}_2(\mathbb{A}_K)$ restricted to that slab. Let $S_K$ be a finite set of finite places, $\xi_K$ a homomorphism from the full idele unit group to $\mathbb{C}^\times$, and $N'$ an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$; assume for every $w\notin S_K$ the double-coset relation $(\mathrm{heckeGen}\,w)^{-1}=\mathrm{centralScalar}(z)\,u_1\,\mathrm{heckeGen}(w)\,u_2$ for some central idele $z$ and some $u_1,u_2$ in $\mathrm{principalLevel}(N')\cap\ker(\mathrm{glArch})$. Let $\mathrm{tys}_K$ be an archimedean type family for $K$ and let $f$ be a continuous, compactly supported function on $\mathrm{GL}_2(\mathbb{A}_K)$ which is unit-factorizable of type $\mathrm{tys}_K$ relative to $\mathrm{principalLevel}(N')\cap\ker(\mathrm{glArch})$ and $S_K$, that is, bi-invariant under that subgroup with the prescribed factorisation into an archimedean factor and a finite factor given by local test functions at $S_K$ and supported on integral components outside $S_K$, and archimedean bi-finite of type $\mathrm{tys}_K$. Form the carrier data $\mathrm{pins}=\mathrm{productionPinsOf}\,K\,D\,(M\mapsto\mathrm{principalLevel}(M)\cap\ker(\mathrm{glArch}))\,\mathrm{heckeGen}\,(\mathrm{adelicBox}\,K)$, carrying the Borel structures, the adelic Haar measures, the full central subgroup and the box-conditioned additive measure. Then the function sending a cuspidal class $\pi$ (a Hecke eigensystem of level $N'$ whose $a_v$ and $b_v$ vanish for $v\in S_K$ and whose isotypic cuspidal submodule is non-zero) to $\|\mathrm{cutTrace}\,K\,\mathrm{pins}\,\xi_K\,N'\,S_K\,\pi\,\mathrm{tys}_K\,f\|$, the norm of the trace of right convolution by $f$ on the intersection of the $\pi$-isotypic cuspidal submodule with the archimedean cut submodule of type $\mathrm{tys}_K$, is summable over those classes.
--
--   This is the absolute-convergence input to the trace formula in the untwisted setting: the spectral side, restricted to the cuspidal classes pinned by a Siegel covering and cut by a finite family of archimedean types, converges absolutely for a unit-factorizable test function. It is used in the comparison of fibre sums of twisted and untwisted cut traces, where rearrangement of the spectral sum over cuspidal classes requires unconditional summability.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre.lean

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

theorem AutomorphicForm.summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre
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
    (hft : IsUnitFactorizableOfTypeAt K tysK (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) SK f) :
    Summable (fun π : ↥(cuspClasses K
        (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N' SK) =>
      ‖cutTrace K
          (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N' SK π tysK f hf hfc‖) := by sorry
