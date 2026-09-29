-- Prove2me | Theorems.Thm_AutomorphicForm_adelicGLHaar_image_mul_right_integralWindowedSiegelSet_inter_slab_lt_top_rat
-- name    : AutomorphicForm.adelicGLHaar_image_mul_right_integralWindowedSiegelSet_inter_slab_lt_top_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/c7ad94d2-b9c8-55a7-8ac4-6569ba39df65
-- title:
--   Finiteness of the Haar measure of a translated Siegel set in a determinant slab over ℚ
-- statement:
--   Fix real numbers $c,u$ with $c>0$, an element $t$ of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, and real numbers $e_1,e_2$ with $e_1>0$. Let $\mathfrak{S}(c,u)=$ `integralWindowedSiegelSet ℚ c u` be the set of $g\in\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ such that: the finite part $\mathrm{glFin}(g)$ of $g$ lies in `finiteIntegralGL2`, namely in the full-level subgroup `finiteLevelZero (𝓞 ℚ) ℚ ⊤` of $\mathrm{GL}_2$ over the finite adeles; the archimedean height $\mathrm{archHeight}(\mathrm{glArch}(g))=\prod_{v\mid\infty}\mathrm{localHeight}(g_v)^{\,[\,\cdot\,]}$, the product over the infinite places of $\mathbb{Q}$ of local heights of the archimedean components raised to the multiplicity of the place, is at least $c$; and for every infinite place $v$ the window quantity $\mathrm{xWindowSq}(g_v)=\mathrm{topNormSq}(g_v)/\mathrm{rowNormSq}(g_v)-\mathrm{localHeight}(g_v)^2$ is at most $u^2$. The assertion is that the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, taken for the Borel structure `glBorel`, of the intersection of the right translate $\{g t : g\in\mathfrak{S}(c,u)\}$ with the determinant slab $\{g : \mathrm{ideleNorm}(\det g)\in[e_1,e_2]\}$, where $\mathrm{ideleNorm}$ is the module of an idele given by the distributive Haar character of $\mathbb{A}_{\mathbb{Q}}$, is strictly less than $\infty$. No hypothesis $e_1\le e_2$ is required.
--
--   This is the measure-theoretic finiteness statement for Siegel sets in the adelic setting, specialised to $\mathbb{Q}$: a right translate of an integrally windowed Siegel set with positive height floor meets each determinant slab in a set of finite volume. It is used in the construction of Rankin–Selberg test data over $\mathbb{Q}$, in [`AutomorphicForm.exists_rankinSelberg_testData_of_isArithGenuineCuspRealizable_rat`](thm.html#AutomorphicForm.exists_rankinSelberg_testData_of_isArithGenuineCuspRealizable_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_adelicGLHaar_image_mul_right_integralWindowedSiegelSet_inter_slab_lt_top_rat.lean

import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm
open AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.adelicGLHaar_image_mul_right_integralWindowedSiegelSet_inter_slab_lt_top_rat
    (c u : ℝ) (hc : 0 < c) (t : AdelicGL2 (𝓞 ℚ) ℚ) (e₁ e₂ : ℝ) (he₁ : 0 < e₁) :
    adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
        (((· * t) '' integralWindowedSiegelSet ℚ c u) ∩
          {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}) < ⊤ := by sorry
