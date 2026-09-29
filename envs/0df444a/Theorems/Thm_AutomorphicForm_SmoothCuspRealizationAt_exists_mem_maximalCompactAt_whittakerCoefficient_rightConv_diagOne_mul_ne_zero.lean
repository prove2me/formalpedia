-- Prove2me | Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_mem_maximalCompactAt_whittakerCoefficient_rightConv_diagOne_mul_ne_zero
-- name    : AutomorphicForm.SmoothCuspRealizationAt.exists_mem_maximalCompactAt_whittakerCoefficient_rightConv_diagOne_mul_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/52c262f0-bc85-524c-8c74-b69bfb8edea0
-- title:
--   Non-vanishing first Whittaker coefficient at a torus point trivial outside S
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals and $T$ a finite set of elements of $\mathrm{GL}_2(\mathbb{A}_K)$, and let the carrier data be the production pins with domain $\bigcup_{x\in T}(\text{centre-cut Siegel set})\cdot x$, level subgroups $N\mapsto U_1(N)\cap\ker(\text{archimedean part})$, Hecke generators $\mathrm{heckeGen}_v$, and the additive box $\mathrm{adelicBox}\,K$ (so the central subgroup is all of $\mathbb{A}_K^\times$ and the additive measure is the adelic Haar measure conditioned to that box). Let $\Theta$ be a Hecke eigensystem over $\mathbb{C}$ and $R$ a smooth cuspidal realisation at these pins for $\Theta.\mathrm{toRawCentral}$ (same level and $a_v$, with $b_v$ divided by the absolute norm of $v$), with $R.\mathrm{toFun}$ continuous and right-invariant under $U_1(\Theta.\mathrm{level})\cap\ker(\text{archimedean part})$. Let $f$ be a factorizable test function, i.e. a product of a compactly supported archimedean factor smooth in the matrix entries and a locally constant compactly supported finite factor, bi-invariant under the same subgroup, and let $S_f,S_\psi\subseteq S$ be finite sets of finite places such that: whenever $f(z)\neq0$, the component of $z$ at each $v\notin S_f$ lies in the local integral set (entries of $z_v$ and $z_v^{-1}$ in $\mathcal{O}_v$) and $z=z_1z_2$ with $z_2\in U_1(\Theta.\mathrm{level})\cap\ker(\text{archimedean part})$ and $z_1$ commuting with the image of $\mathrm{GL}_2(K_v)$ for every $v\notin S_f$; for $v\notin S$, $v$ does not divide $\Theta.\mathrm{level}$ and $v\notin R.\mathrm{exceptionalSet}$; and for $v\notin S_\psi$ the local component at $v$ of the standard additive character has level $0$. Assume further that the right convolution $g\mapsto\int R(gx)f(x)\,dx$ is a smooth cuspidal automorphic function at these pins with central character $R.\mathrm{centralChar}$, and is not identically zero. Then there exist an idele $t_0\in\mathbb{A}_K^\times$ and $k_0$ in the maximal compact subgroup at $S$ (integral finite part, row-isometric archimedean components, trivial finite component outside $S$) such that the component of $t_0$ at every finite $v\notin S$ equals $1$ and the Whittaker coefficient at $\alpha=1$, taken against the standard global additive character, of the convolved form is non-zero at $\mathrm{diag}(t_0,1)\,k_0$.
--
--   This is the non-degeneracy statement for the first Fourier–Whittaker coefficient of a smoothed cusp form: the coefficient is shown to be non-zero at a point of the diagonal torus whose components away from the finite set $S$ are trivial, so that the non-vanishing point can be coupled with unramified local computations at the places outside $S$. It serves as the input for the construction of Rankin–Selberg test data with non-vanishing $s$-part integral, both in the self-paired and the two-form case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_mem_maximalCompactAt_whittakerCoefficient_rightConv_diagOne_mul_ne_zero.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp IsDedekindDomain

theorem AutomorphicForm.SmoothCuspRealizationAt.exists_mem_maximalCompactAt_whittakerCoefficient_rightConv_diagOne_mul_ne_zero
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (Θ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral R)
    (hRlev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K,
      R.toFun (g * k) = R.toFun g)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hfT : IsFactorizableTestFn K f)
    (S Sf Sψ : Finset (HeightOneSpectrum (𝓞 K))) (hSf : Sf ⊆ S) (hSψ : Sψ ⊆ S)
    (hfsupp : ∀ z : AdelicGL2 (𝓞 K) K, f z ≠ 0 →
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
        finComponent (𝓞 K) K v (glFin (𝓞 K) K z) ∈ localIntegralSet K v) ∧
      ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K, z = z₁ * z₂ ∧
        z₂ ∈ levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K ∧
        ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf → ∀ xv : GL (Fin 2) (v.adicCompletion K),
          z₁ * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * z₁)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ¬ v.asIdeal ∣ Θ.level ∧ v ∉ R.exceptionalSet)
    (hSψ0 : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sψ →
      LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K v) = 0)
    (hfbi : ∀ k ∈ levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K, ∀ z : AdelicGL2 (𝓞 K) K,
      f (k * z) = f z ∧ f (z * k) = f z)
    (hx₀ : IsSmoothCuspAutomorphicFnAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) R.centralChar (rightConv K R.toFun f))
    (hne : ∃ g : AdelicGL2 (𝓞 K) K, rightConv K R.toFun f g ≠ 0) :
    ∃ (t₀ : (AdeleRing (𝓞 K) K)ˣ) (k₀ : AdelicGL2 (𝓞 K) K),
      k₀ ∈ maximalCompactAt K S ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((t₀ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1) ∧
      whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) 1 (diagOne t₀ * k₀) ≠ 0 := by sorry
