-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_dynamically_convex_on_strictly_convex_star_shaped_points
-- name    : BirkhoffGlobalSection.dynamically_convex_on_strictly_convex_star_shaped_points
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-28T03:12:31.182585+00:00
-- url     : https://prove2.me/theorems/0dd652a3-7869-4583-8992-5ff7af05220e
-- title:
--   Strictly convex star-shaped points carry index at least three
-- statement:
--   A local Conley–Zehnder index bound on strictly convex, star-shaped parts of an energy surface in $\mathbb{R}^4$.
--
--   Let $G:\mathbb{R}^4\to\mathbb{R}$ be any Hamiltonian. Let $x$ be a closed orbit of its Hamiltonian flow, $\dot x=X_G(x)$ and $x(T)=x(0)$ for some $T>0$. Suppose that at every point $x(t)$ the function $G$ is $C^2$ nearby and
--
--   $$
--   dG_{x(t)}\big(x(t)\big)>0,\qquad D^2G_{x(t)}(v,v)>0\quad\text{for all } v\neq0 \text{ with } dG_{x(t)}(v)=0 .
--   $$
--
--   Then the orbit has transverse winding above one in the global quaternionic frame. Equivalently, its Conley–Zehnder index is at least $3$, where degenerate orbits use the lower semicontinuous extension. In other words, the flow of $G$ is dynamically convex on the set of strictly convex star-shaped points of its level sets.
--
--   This is the pointwise form of the theorem of Hofer–Wysocki–Zehnder that strictly convex energy surfaces in $\mathbb{R}^4$ are dynamically convex. The index of a closed orbit is determined by the Hamiltonian along the orbit, as observed in Liu–Salomão, Proposition 1.11. The statement needs no global hypothesis on the energy surface.
--
--   **Formalization Note** The conclusion is `IsDynamicallyConvexOn G {y | IsStrictlyConvexStarShapedAt G y}`, using `Def_BirkhoffGlobalSection_DynamicalConvexity` and `Def_BirkhoffGlobalSection_RegularizationModel`. Multiple covers are included.
-- source:
--   Hofer--Wysocki--Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998) (strictly convex energy surfaces are dynamically convex). Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2, Proposition 1.11 and its proof (the index depends only on the Hamiltonian near the orbit).

import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity
import Definitions.Def_BirkhoffGlobalSection_RegularizationModel

namespace BirkhoffGlobalSection

/-- Local index bound for strictly convex star-shaped levels. For every
Hamiltonian `G` on `ℝ⁴`, every closed orbit made of points at which the level
set of `G` is strictly convex and star-shaped has transverse winding above one,
that is, Conley--Zehnder index at least `3`. This is the pointwise form of the
Hofer--Wysocki--Zehnder theorem that strictly convex energy surfaces are
dynamically convex; the index only depends on the Hamiltonian near the orbit,
as in Liu--Salomao, Proposition 1.11. -/
theorem dynamically_convex_on_strictly_convex_star_shaped_points
    (G : Phase → ℝ) :
    IsDynamicallyConvexOn G {y : Phase | IsStrictlyConvexStarShapedAt G y} := by
  sorry

end BirkhoffGlobalSection
