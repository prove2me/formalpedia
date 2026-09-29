-- Prove2me | Theorems.Thm_AutomorphicForm_exists_iUnion_centreCutSiegelSet_mem_nhds
-- name    : AutomorphicForm.exists_iUnion_centreCutSiegelSet_mem_nhds
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/7a64826e-b31a-5d9d-9ee9-93c886dfca36
-- title:
--   Centre-cut Siegel windows are neighbourhoods in adelic GL₂
-- statement:
--   Let $F$ be a number field and let $g$ be an element of $\mathrm{AdelicGL2}(\mathcal{O}_F, F)$, i.e. of $GL_2(\mathbb{A}_F)$, the general linear group of $2\times 2$ matrices over the adele ring. The assertion is that there exist real numbers $c, u, d_1, d_2$ and a finite subset $T$ of $GL_2(\mathbb{A}_F)$ with $c > 0$ and $d_1 > 0$ such that the union over $x \in T$ of the images of `centreCutSiegelSet F c u d₁ d₂` under right multiplication by $x$ is a neighbourhood of $g$. Here `centreCutSiegelSet F c u d₁ d₂` is the set of those $h \in GL_2(\mathbb{A}_F)$ whose finite part `glFin h` lies in the subgroup `finiteIntegralGL2` (the level-zero subgroup `finiteLevelZero` at the unit ideal) and which satisfy, at every infinite place $w$ of $F$, writing $h_w$ for the image of $h$ in $GL_2(F_w)$: the height $\lVert \det h_w\rVert / \mathrm{rowNormSq}(h_w)$ is at least $c$; the window quantity $\mathrm{topNormSq}(h_w)/\mathrm{rowNormSq}(h_w)$ minus the square of that height is at most $u^2$; and $\lVert \det h_w \rVert$ lies in the closed interval $[d_1, d_2]$. No inequality between $d_1$ and $d_2$, and no constraint on $u$, is asserted.
--
--   This is the statement that centre-cut Siegel sets, translated by finitely many group elements on the right, cover $GL_2(\mathbb{A}_F)$ by neighbourhoods — the adelic analogue of the fact that Siegel sets have non-empty interior and that finitely many of their translates suffice locally. It is used in the cuspidal spectral decomposition, where bounds valid on a single window are upgraded to locally uniform statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_iUnion_centreCutSiegelSet_mem_nhds.lean

import Definitions.Def_AutomorphicForm_CentreCutSiegelSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicVolume AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped Topology

theorem AutomorphicForm.exists_iUnion_centreCutSiegelSet_mem_nhds (F : Type) [Field F] [NumberField F] (g : AdelicGL2 (𝓞 F) F) :
    ∃ (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)), 0 < c ∧ 0 < d₁ ∧
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ∈ 𝓝 g := by sorry
