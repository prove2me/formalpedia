-- Prove2me | Theorems.Thm_AutomorphicForm_exists_iUnion_image_mul_centreCutSiegelSet_subset_setOf_ideleNorm_det_mem_Icc
-- name    : AutomorphicForm.exists_iUnion_image_mul_centreCutSiegelSet_subset_setOf_ideleNorm_det_mem_Icc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/6084aaaf-cf09-55d7-8dac-11208b8a41ee
-- title:
--   Translates of a centre-cut Siegel set lie in a determinant slab
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $0<d_1$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb A_K)$ (the group `AdelicGL2 (𝓞 K) K` of invertible $2\times 2$ matrices over the adele ring). Write $\mathfrak S=$ `centreCutSiegelSet K c u d₁ d₂` for the set of $g\in\mathrm{GL}_2(\mathbb A_K)$ such that: the finite component `glFin (𝓞 K) K g` lies in the subgroup `finiteIntegralGL2 (𝓞 K) K`, namely `finiteLevelZero (𝓞 K) K ⊤`; for every infinite place $w$ of $K$ the component $g_w\in\mathrm{GL}_2(K_w)$ of the archimedean part satisfies $c\le \|\det g_w\|/\mathrm{rowNormSq}(g_w)$, satisfies $\mathrm{topNormSq}(g_w)/\mathrm{rowNormSq}(g_w)-\bigl(\|\det g_w\|/\mathrm{rowNormSq}(g_w)\bigr)^2\le u^2$, and satisfies $\|\det g_w\|\in[d_1,d_2]$. Then there exist real $\alpha,\beta$ with $0<\alpha$ such that the union over $x\in T$ of the right translates $\mathfrak S\,x=\{g x: g\in\mathfrak S\}$ is contained in the set of those $g$ whose idele norm of $\det g$ — the value at the unit $\det g$ of the distributive Haar character of the adele ring, viewed as a real number — lies in $[\alpha,\beta]$. Only positivity of $\alpha$ is asserted; $\alpha\le\beta$ is not part of the conclusion.
--
--   This is the standard fact that a Siegel set with determinants constrained at the infinite places, and any finite set of its right translates, meets only a compact range of idelic determinant norms: the adelic determinant is pinched between positive constants. It provides the carrier estimate used in the convergence and cusp-form arguments for automorphic functions on $\mathrm{GL}_2(\mathbb A_K)$, where integrals and sums over such a union are compared after rescaling by a power of $\|\det\|_{\mathbb A}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_iUnion_image_mul_centreCutSiegelSet_subset_setOf_ideleNorm_det_mem_Icc.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_iUnion_image_mul_centreCutSiegelSet_subset_setOf_ideleNorm_det_mem_Icc
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (T : Finset (AdelicGL2 (𝓞 K) K)) :
    ∃ α β : ℝ, 0 < α ∧
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) ⊆
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} := by sorry
