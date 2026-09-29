-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre
-- name    : AutomorphicForm.exists_finset_central_slab_covering_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/bc7f9d3d-8011-545d-b5ee-a6078043a7c9
-- title:
--   Determinant slabs are covered with finitely many central ideles
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $\mathfrak{S}=$ `centreCutSiegelSet F c u d₁ d₂` be the set of $g\in\mathrm{GL}_2(\mathbb{A}_F)$ whose finite component `glFin` lies in the subgroup `finiteIntegralGL2` ($=$ `finiteLevelZero` at the unit ideal) and whose archimedean component satisfies, at every infinite place $w$ of $F$: $c\le$ `localHeight` of the $w$-component, i.e. $\|\det\|/$`rowNormSq`; `xWindowSq` of that component, i.e. `topNormSq`$/$`rowNormSq` minus the square of the height, at most $u^2$; and `archDetNorm` $w$ $g=\|\det\|$ of the $w$-component in $[d_1,d_2]$. Let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$ and assume `CoversModCentre` for $\bigcup_{x\in T}\mathfrak{S}x$: every $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g\,(z\cdot 1_2)\in\mathfrak{S}x$ for some $x\in T$, where $\gamma$ and $z$ act through `globalPoints` and `centralScalar`. Let $\alpha,\beta$ be real with $0<\alpha$. Then there is a finite set $N$ of idele units of $F$ such that for every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ with `ideleNorm` of $\det g$ (the value of the distributive Haar character, as a real number) lying in $[\alpha,\beta]$, there exist $\gamma\in\mathrm{GL}_2(F)$, $n\in N$ and $x\in T$ with $\gamma g\in\mathfrak{S}\cdot\bigl((n\cdot 1_2)\,x\bigr)$.
--
--   This is the determinant-slab form of reduction theory for $\mathrm{GL}_2$ over a number field: on a slab $\alpha\le\|\det g\|\le\beta$ the central idele needed to push $g$ into the given union of translated centre-cut Siegel sets may be taken from one finite set, and the resulting translating element is displayed as a central scalar times an element of $T$. It is used in the volume and $L^2$ estimates for the cuspidal spectrum, where a fundamental-domain-type covering with finitely many explicit translates is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.exists_finset_central_slab_covering_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (α β : ℝ) (hα : 0 < α) :
    ∃ N : Finset (AdeleRing (𝓞 F) F)ˣ, ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β →
        ∃ γ : GL (Fin 2) F, ∃ n ∈ N, ∃ x ∈ T,
          globalPoints (𝓞 F) F γ * g ∈
            (· * (centralScalar (𝓞 F) F n * x)) '' centreCutSiegelSet F c u d₁ d₂ := by sorry
