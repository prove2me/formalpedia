-- Prove2me | Theorems.Thm_AutomorphicForm_ne_zero_of_coversModCentre_iUnion_centreCutSiegelSet
-- name    : AutomorphicForm.ne_zero_of_coversModCentre_iUnion_centreCutSiegelSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/f92d52cb-7eda-5ff6-a6c9-69900ffe34c3
-- title:
--   Covering by centre-cut Siegel windows forces u ≠ 0
-- statement:
--   Let $F$ be a number field, and let $c, u, d_1, d_2$ be real numbers and $T$ a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$, the group `AdelicGL2 (𝓞 F) F` of invertible $2\times 2$ matrices over the adele ring of $F$. The centre-cut Siegel set `centreCutSiegelSet F c u d₁ d₂` consists of those $g \in \mathrm{GL}_2(\mathbb{A}_F)$ whose finite component `glFin (𝓞 F) F g` lies in the subgroup `finiteIntegralGL2 (𝓞 F) F` (the level-zero subgroup at the unit ideal) and which satisfy, at every infinite place $w$ of $F$, writing $g_w$ for the image of $g$ in $\mathrm{GL}_2(F_w)$ under `archComponent F w ∘ glArch (𝓞 F) F`: first $c \le |\det g_w| / \mathrm{rowNormSq}(g_w)$; second $\mathrm{topNormSq}(g_w)/\mathrm{rowNormSq}(g_w) - (|\det g_w|/\mathrm{rowNormSq}(g_w))^2 \le u^2$; and third $|\det g_w| \in [d_1, d_2]$. Assume the hypothesis `CoversModCentre F` for the union $\bigcup_{x \in T}$ of the right translates by $x$ of this set, that is: for every $g \in \mathrm{GL}_2(\mathbb{A}_F)$ there exist $\gamma \in \mathrm{GL}_2(F)$ and $z \in \mathbb{A}_F^{\times}$ such that the image of $\gamma$ under `globalPoints`, times $g$, times the central scalar matrix attached to $z$, lies in that union. The conclusion is that $u \neq 0$.
--
--   A non-degeneracy statement for the horizontal (unipotent) window parameter of an adelic Siegel set: no finite union of right translates of a centre-cut Siegel set with a degenerate $x$-window can meet every coset $\mathrm{GL}_2(F)\, g\, Z(\mathbb{A}_F)$. It is used as a standing hypothesis-cleaning step in the later results on archimedean occurrence in a class and on $L^2$-membership of forms bounded on Siegel windows.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_ne_zero_of_coversModCentre_iUnion_centreCutSiegelSet.lean

import Definitions.Def_AutomorphicForm_SiegelCovering

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering

theorem AutomorphicForm.ne_zero_of_coversModCentre_iUnion_centreCutSiegelSet
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) :
    u ≠ 0 := by sorry
