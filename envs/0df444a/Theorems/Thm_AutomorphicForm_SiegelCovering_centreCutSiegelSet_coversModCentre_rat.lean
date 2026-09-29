-- Prove2me | Theorems.Thm_AutomorphicForm_SiegelCovering_centreCutSiegelSet_coversModCentre_rat
-- name    : AutomorphicForm.SiegelCovering.centreCutSiegelSet_coversModCentre_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/6acbfbe6-dc49-5aa9-88dc-b468b5fbcfca
-- title:
--   Centre-cut Siegel sets cover adelic GL₂ over ℚ
-- statement:
--   Let $c, u, d_1, d_2$ be real numbers satisfying $c \le \sqrt{3}/2$, $1/2 \le u$, $0 < d_2$ and $d_1 \le d_2$. Then the centre-cut Siegel set $\mathfrak{S} =$ `centreCutSiegelSet ℚ c u d₁ d₂` inside $\mathrm{GL}_2$ of the adele ring of $\mathbb{Q}$ (taken over $\mathcal{O}_{\mathbb{Q}}$) covers the whole group modulo global points and the centre: for every $g \in \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ there are $\gamma \in \mathrm{GL}_2(\mathbb{Q})$ and a unit $z$ of $\mathbb{A}_{\mathbb{Q}}$ such that the product of the image of $\gamma$ under the entrywise map $\mathrm{GL}_2(\mathbb{Q}) \to \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, of $g$, and of the scalar matrix $z$ lies in $\mathfrak{S}$. Here $\mathfrak{S}$ consists of those $h$ whose finite component `glFin` lies in the subgroup `finiteIntegralGL2` (level-zero subgroup at the unit ideal) and whose archimedean components satisfy, at every infinite place $w$ of $\mathbb{Q}$: $c \le \|\det\|/\mathrm{rowNormSq}$ for the $w$-component of the archimedean part; $\mathrm{topNormSq}/\mathrm{rowNormSq} - (\|\det\|/\mathrm{rowNormSq})^2 \le u^2$; and the norm of the determinant of the $w$-component lies in $[d_1, d_2]$.
--
--   This is reduction theory for $\mathrm{GL}_2$ over $\mathbb{Q}$ in adelic form, the assertion $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}) = \mathrm{GL}_2(\mathbb{Q}) \cdot \mathfrak{S} \cdot Z(\mathbb{A}_{\mathbb{Q}})$ for a Siegel set cut by a determinant-norm window, with the numerical constants $\sqrt{3}/2$ and $1/2$ coming from the standard fundamental domain for $\mathrm{SL}_2(\mathbb{Z})$ on the upper half-plane. It is the covering input for the construction of adelic fundamental domains used in the passage between classical cusp forms and adelic automorphic forms, and is cited by the production covering statement for the domain $D$ over $\mathbb{Q}$ and by the realizability and newform-span results built on it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SiegelCovering_centreCutSiegelSet_coversModCentre_rat.lean

import Definitions.Def_AutomorphicForm_SiegelCovering

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AutomorphicForm.SiegelCovering.centreCutSiegelSet_coversModCentre_rat {c u d₁ d₂ : ℝ}
    (hc : c ≤ Real.sqrt 3 / 2) (hu : 1 / 2 ≤ u) (hd₂ : 0 < d₂) (hd : d₁ ≤ d₂) :
    AutomorphicForm.SiegelCovering.CoversModCentre ℚ
      (AutomorphicForm.WindowedSiegel.centreCutSiegelSet ℚ c u d₁ d₂) := by sorry
