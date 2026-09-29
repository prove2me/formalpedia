-- Prove2me | Theorems.Thm_AutomorphicForm_not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero
-- name    : AutomorphicForm.not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/7ba68845-9561-5c07-8079-375dda24d31c
-- title:
--   Zero x-window centre-cut Siegel sets never cover modulo centre
-- statement:
--   Let $F$ be a number field, let $c, d_1, d_2$ be real numbers, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$, where $\mathbb{A}_F$ denotes the adele ring of $F$ over $\mathcal{O}_F$. Write $\mathfrak{S} =$ `centreCutSiegelSet F c 0 d₁ d₂` for the set of $g \in \mathrm{GL}_2(\mathbb{A}_F)$ whose finite component `glFin` lies in the subgroup `finiteIntegralGL2` (namely `finiteLevelZero` at the unit ideal), and which satisfy, at every infinite place $w$ of $F$, writing $g_w$ for the image of $g$ in $\mathrm{GL}_2(F_w)$ under `glArch` followed by `archComponent`: first $c \le \lVert \det g_w \rVert / \mathrm{rowNormSq}(g_w)$; second $\mathrm{topNormSq}(g_w)/\mathrm{rowNormSq}(g_w) - (\lVert \det g_w\rVert/\mathrm{rowNormSq}(g_w))^2 \le 0^2 = 0$, i.e. the squared $x$-window vanishes identically rather than merely being bounded; and third $\lVert \det g_w \rVert \in [d_1, d_2]$. The theorem asserts that the union $\bigcup_{x \in T} \mathfrak{S}x$ of the right translates of $\mathfrak{S}$ by the elements of $T$ does not satisfy `CoversModCentre F`, that is: it is false that for every $g \in \mathrm{GL}_2(\mathbb{A}_F)$ there exist $\gamma \in \mathrm{GL}_2(F)$ and $z \in \mathbb{A}_F^\times$ with $\gamma g \cdot z I$ in that union, the rational point $\gamma$ and the central scalar $z$ being mapped in via `globalPoints` and `centralScalar`. No inequality between $d_1$ and $d_2$ is assumed.
--
--   This is the degeneracy statement of the reduction theory used here: a centre-cut Siegel window with $x$-parameter $0$ is too thin to serve as a fundamental set for $\mathrm{GL}_2(F) \backslash \mathrm{GL}_2(\mathbb{A}_F) / Z(\mathbb{A}_F)$, however large the remaining parameters and however many right translates are taken. It is used in contrapositive form to conclude that a covering family of centre-cut Siegel sets must have nonzero $x$-window, and thence in the bound on the values of an $L^p$ automorphic form along archimedean central units.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero.lean

import Definitions.Def_AutomorphicForm_SiegelCovering

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering

theorem AutomorphicForm.not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero
    (F : Type) [Field F] [NumberField F] (c d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) :
    ¬ CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c 0 d₁ d₂) := by sorry
