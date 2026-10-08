-- Prove2me | Theorems.Thm_AssocRealizations_SantosFan_theorem_5_2
-- name    : AssocRealizations.SantosFan.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:36.860841+00:00
-- url     : https://prove2.me/theorems/be38e638-1809-4b6a-bec4-10f838693615
-- title:
--   Theorems 5.1–5.2 — Santos' fan is a complete simplicial fan and the normal fan of an n-dimensional associahedron
-- statement:
--   Let $n \ge 0$, let $T_0$ be a triangulation of the convex $(n+3)$-gon, and let $v_{pq} \in V = \mathbb R^{T_0}$ be Santos' vectors ($v_{pq} = -\alpha_\delta$ if $pq = \delta \in T_0$, otherwise the sum of the $\alpha_\delta$ over the seed diagonals $\delta$ crossed by $pq$). Then:
--   1. (Theorem 5.1) the cones $\mathbb R_{\ge0}T$, $T$ a triangulation, form a complete simplicial fan $\mathcal F_{T_0}$ in $V$;
--   2. (Theorem 5.2) $\mathcal F_{T_0}$, the set of cones $\mathbb R_{\ge0}D$ over all sets $D$ of pairwise non-crossing diagonals, is the normal fan of a polytope: there is a polytope $P \subseteq V$ with
--   $$\mathcal F_{T_0} = \{\, N_P(x) : x \in P \,\}, \qquad N_P(x) = \Big\{c : \textstyle\sum_\delta c_\delta y_\delta \le \sum_\delta c_\delta x_\delta \ \forall y \in P\Big\}.$$
--
--   Such a polytope is an $n$-dimensional associahedron: its nonempty faces correspond, reversing inclusion, to the cones of its normal fan, which are in bijection with the non-crossing sets of diagonals; and $\{0\} \in \mathcal F_{T_0}$ forces $P$ to be full-dimensional. These are Santos' "type II" associahedra; the snake seed gives the Chapoton–Fomin–Zelevinsky associahedron.
--
--   **Formalization Note** The polytope is specified through its normal fan only, as in the paper's statement. Exterior normal cones are used (p. 5), and linear functionals are identified with vectors of $\mathbb R^{T_0}$ by the coordinate pairing. The first conjunct repeats Theorem 5.1, to which the theorem refers ("This fan"), so the goal is self-contained.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 19, Theorems 5.1 and 5.2

import Mathlib
import Definitions.Def_AssocRealizations_SantosFan_Setting

namespace AssocRealizations.SantosFan

open ChvatalArtGallery.FanPartition

/-- Theorems 5.1 and 5.2 (p. 19): for every seed triangulation `T₀` of the `(n + 3)`-gon, the
cones `ℝ≥0 T` of Santos' vectors form a complete simplicial fan `𝓕_{T₀}`, and `𝓕_{T₀}` is the
normal fan of a polytope (necessarily an `n`-dimensional associahedron). -/
theorem theorem_5_2 (n : ℕ) (T₀ : Finset (Sym2 (Fin (n + 3))))
    (h₀ : IsTriangulation (n + 3) T₀) :
    IsCompleteSimplicialFan (AssocRealizations.TypesMeet.santosVec T₀) ∧
      ∃ P : Set ({d // d ∈ T₀} → ℝ), IsNormalFanOf (AssocRealizations.TypesMeet.santosFan T₀) P := by sorry

end AssocRealizations.SantosFan
