-- Prove2me | Theorems.Thm_AssocRealizations_SantosFan_theorem_5_1
-- name    : AssocRealizations.SantosFan.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:25.704881+00:00
-- url     : https://prove2.me/theorems/7cb46a17-de2f-48d2-a6e9-a9ba6401a759
-- title:
--   Theorem 5.1 — Santos' cones of all triangulations form a complete simplicial fan
-- statement:
--   Let $n \ge 0$, let $T_0$ be a triangulation of the convex $(n+3)$-gon, and let $v_{pq} \in V = \mathbb R^{T_0}$ be Santos' vectors: $v_{pq} = -\alpha_\delta$ if $pq = \delta \in T_0$, and $v_{pq} = \sum_{\delta \in T_0 \text{ crossed by } pq} \alpha_\delta$ otherwise. Then the simplicial cones
--   $$\mathbb R_{\ge 0} T = \mathrm{cone}\{v_e : e \in T\}, \qquad T \text{ a triangulation of the } (n+3)\text{-gon},$$
--   form a complete simplicial fan $\mathcal F_{T_0}$ in $V$:
--   1. for every triangulation $T$ the $n$ vectors $v_e$, $e \in T$, are linearly independent;
--   2. every vector of $V$ lies in $\mathbb R_{\ge0}T$ for some triangulation $T$;
--   3. for any two triangulations $T, T'$, $\mathbb R_{\ge0}T \cap \mathbb R_{\ge0}T' = \mathbb R_{\ge0}(T \cap T')$.
--
--   This is the first half of Santos' construction: it produces, for each seed triangulation, a complete fan whose face structure is that of the associahedron. Theorem 5.2 shows that this fan is moreover the normal fan of a polytope.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 19, Theorem 5.1

import Mathlib
import Definitions.Def_AssocRealizations_SantosFan_Setting

namespace AssocRealizations.SantosFan

open ChvatalArtGallery.FanPartition

/-- Theorem 5.1 (p. 19): for every seed triangulation `T₀` of the `(n + 3)`-gon, the cones
`ℝ≥0 T` of Santos' vectors over all triangulations `T` form a complete simplicial fan in
`V = ℝ^{T₀}`. -/
theorem theorem_5_1 (n : ℕ) (T₀ : Finset (Sym2 (Fin (n + 3))))
    (h₀ : IsTriangulation (n + 3) T₀) :
    IsCompleteSimplicialFan (AssocRealizations.TypesMeet.santosVec T₀) := by sorry

end AssocRealizations.SantosFan
