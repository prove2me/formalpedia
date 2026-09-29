-- Prove2me | Theorems.Thm_AutomorphicForm_coversModCentre_of_le_of_lt_of_coversModCentre
-- name    : AutomorphicForm.coversModCentre_of_le_of_lt_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/109ac426-5ec2-5dd6-ba7e-8a511fe64df1
-- title:
--   Raising the lower determinant bound preserves covering modulo the centre
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2,d_1'$ be real numbers, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$, the adelic group `AdelicGL2 (𝓞 F) F` of invertible $2\times 2$ matrices over the adele ring of $F$. For parameters $a,b$ the set `centreCutSiegelSet F c u a b` consists of those $g\in\mathrm{GL}_2(\mathbb{A}_F)$ whose finite component `glFin` lies in the subgroup `finiteIntegralGL2 (𝓞 F) F` (the full level-zero subgroup `finiteLevelZero (𝓞 F) F ⊤`) and which satisfy, at every infinite place $w$ of $F$, writing $g_w$ for the image of $g$ under `glArch` followed by `archComponent F w`: $c \le \lVert\det g_w\rVert/\mathrm{rowNormSq}(g_w)$, the horizontal window bound $\mathrm{xWindowSq}(g_w)=\mathrm{topNormSq}(g_w)/\mathrm{rowNormSq}(g_w)-\bigl(\lVert\det g_w\rVert/\mathrm{rowNormSq}(g_w)\bigr)^2\le u^2$, and $\mathrm{archDetNorm}\,w\,g=\lVert\det g_w\rVert\in[a,b]$. Assume $d_1\le d_1'$ and $d_1'<d_2$, and assume that the union $\bigcup_{x\in T}\{s x : s\in \mathrm{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2\}$ satisfies `CoversModCentre F`, i.e. for every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ there are $\gamma\in\mathrm{GL}_2(F)$ and a unit $z$ of $\mathbb{A}_F$ with $\mathrm{globalPoints}(\gamma)\,g\,\mathrm{centralScalar}(z)$ in that union. Then the corresponding union formed from `centreCutSiegelSet F c u d₁' d₂` also satisfies `CoversModCentre F`.
--
--   This is the covering half of the step that narrows the archimedean determinant window of a finite union of right translates of centre-cut Siegel sets: the lower determinant bound may be raised, as long as it stays below the upper bound, without losing surjectivity modulo $\mathrm{GL}_2(F)$ on the left and the adelic centre on the right. It is used in the construction of cuspidal constituents, where test functions and cusp forms are handled on a determinant-cut piece of the adelic group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_coversModCentre_of_le_of_lt_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.coversModCentre_of_le_of_lt_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ d₁' : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hle : d₁ ≤ d₁') (hlt : d₁' < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) :
    CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂) := by sorry
