-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_globalPoints_mul_mul_centralScalar_mem_of_coversModCentre_of_ideleNorm_det_mem_Icc
-- name    : AutomorphicForm.exists_finset_globalPoints_mul_mul_centralScalar_mem_of_coversModCentre_of_ideleNorm_det_mem_Icc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/b95672c4-cb12-5d3b-89a8-49484aa798ce
-- title:
--   Finite central set suffices on a determinant slab
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$, the group of units of $2\times 2$ matrices over the adele ring of $F$. Write $\mathfrak S = \mathrm{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2$ for the set of $g \in \mathrm{GL}_2(\mathbb{A}_F)$ whose finite component `glFin` lies in the subgroup `finiteIntegralGL2` (that is, `finiteLevelZero (𝓞 F) F ⊤`) and which satisfy, at every infinite place $w$ of $F$, with $g_w$ the image of $g$ in $\mathrm{GL}_2(F_w)$: $\lvert\det g_w\rvert/\mathrm{rowNormSq}(g_w) \ge c$; $\mathrm{topNormSq}(g_w)/\mathrm{rowNormSq}(g_w) - (\lvert\det g_w\rvert/\mathrm{rowNormSq}(g_w))^2 \le u^2$; and $\lvert\det g_w\rvert \in [d_1,d_2]$. Let $D = \bigcup_{x \in T} \mathfrak S x$, and assume $D$ covers modulo the centre, i.e. for every $g \in \mathrm{GL}_2(\mathbb{A}_F)$ there are $\gamma \in \mathrm{GL}_2(F)$ and an idele $z$ with $\gamma g \cdot z I \in D$, where $\gamma$ and $z$ act through `globalPoints` and `centralScalar`. Then for all reals $0 < e_1 \le e_2$ there is a finite set $Z$ of ideles such that every $g \in \mathrm{GL}_2(\mathbb{A}_F)$ with idelic modulus $\lVert \det g\rVert_{\mathbb{A}} \in [e_1,e_2]$ admits $\gamma \in \mathrm{GL}_2(F)$ and $z \in Z$ with $\gamma g \cdot z I \in D$.
--
--   This is the reduction-theoretic statement that on a slab where the idelic modulus of the determinant is bounded above and below, the central idele occurring in the covering property $\mathrm{GL}_2(\mathbb{A}_F) = \mathrm{GL}_2(F)\,D\,Z(\mathbb{A}_F)$ may be taken from a fixed finite set. It is used in the construction of ample centre-cut Siegel windows and in the comparison of integrals of functions with fixed central character over a fundamental domain with their mass over the covering window.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_globalPoints_mul_mul_centralScalar_mem_of_coversModCentre_of_ideleNorm_det_mem_Icc.lean

import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.exists_finset_globalPoints_mul_mul_centralScalar_mem_of_coversModCentre_of_ideleNorm_det_mem_Icc
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ ≤ e₂) :
    ∃ Z : Finset (AdeleRing (𝓞 F) F)ˣ, ∀ g : AdelicGL2 (𝓞 F) F,
      ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
        ∃ γ : Matrix.GeneralLinearGroup (Fin 2) F, ∃ z ∈ Z,
          globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z ∈
            ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂ := by sorry
