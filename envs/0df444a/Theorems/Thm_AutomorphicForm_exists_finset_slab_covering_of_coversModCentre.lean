-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_slab_covering_of_coversModCentre
-- name    : AutomorphicForm.exists_finset_slab_covering_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/54174e4e-8dff-5d20-9454-082290cfb5fc
-- title:
--   Determinant slabs are covered without the centre
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and write $\mathfrak S=\mathrm{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2$ for the set of $g\in\mathrm{GL}_2(\mathbb A_F)$ whose finite component $\mathrm{glFin}(g)$ lies in the subgroup `finiteIntegralGL2` (the finite level-zero subgroup at level $\top$) and which satisfy, at every infinite place $w$ of $F$, writing $g_w$ for the image of $g$ under $\mathrm{glArch}$ followed by $\mathrm{archComponent}$ at $w$: $c\le \mathrm{localHeight}(g_w)=\|\det g_w\|/\mathrm{rowNormSq}(g_w)$, $\mathrm{xWindowSq}(g_w)=\mathrm{topNormSq}(g_w)/\mathrm{rowNormSq}(g_w)-\mathrm{localHeight}(g_w)^2\le u^2$, and $\mathrm{archDetNorm}_w(g)=\|\det g_w\|\in[d_1,d_2]$. Let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb A_F)$ and assume that the union $\bigcup_{x\in T}\mathfrak S\,x$ of right translates satisfies `CoversModCentre`: for every $g\in\mathrm{GL}_2(\mathbb A_F)$ there are $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g\,z\in\bigcup_{x\in T}\mathfrak S\,x$, where $\gamma$ and $z$ act through `globalPoints` and `centralScalar`. Then for all real $\alpha,\beta$ with $0<\alpha$ there is a finite subset $T'$ of $\mathrm{GL}_2(\mathbb A_F)$ such that every $g$ whose determinant has idele norm $\mathrm{ideleNorm}_F(\det g)\in[\alpha,\beta]$, this norm being the value of the distributive Haar character of $\mathbb A_F$ at $\det g$, satisfies $\gamma g\in\bigcup_{x\in T'}\mathfrak S\,x$ for some $\gamma\in\mathrm{GL}_2(F)$.
--
--   This is the determinant-slab form of reduction theory for $\mathrm{GL}_2$ over a number field: a covering of $\mathrm{GL}_2(\mathbb A_F)$ by finitely many right translates of a centre-cut Siegel set modulo global points and the centre can be converted, on each region where the idelic determinant norm lies in a fixed interval $[\alpha,\beta]$ with $\alpha>0$, into a covering modulo global points alone, at the cost of enlarging the finite set of translates. It feeds the finiteness of the adelic Haar volume of such determinant slabs, the approximation of automorphic kernels by finite sums of translates, and the compactness of the cuspidal convolution operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_slab_covering_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.exists_finset_slab_covering_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (α β : ℝ) (hα : 0 < α) :
    ∃ T' : Finset (AdelicGL2 (𝓞 F) F), ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β →
        ∃ γ : GL (Fin 2) F,
          globalPoints (𝓞 F) F γ * g ∈ ⋃ x ∈ T', (· * x) '' centreCutSiegelSet F c u d₁ d₂ := by sorry
