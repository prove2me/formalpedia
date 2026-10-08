-- Prove2me | Theorems.Thm_EdgeTransBiCayley_BiAbelian_proposition_1_3
-- name    : EdgeTransBiCayley.BiAbelian.proposition_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:36:43.514798+00:00
-- url     : https://prove2.me/theorems/9e00b5d5-9802-4dea-b0d1-9ead7dba2cb1
-- title:
--   Proposition 1.3 — edge-transitive bi-abelian graphs and minimum valency
-- statement:
--   Let $\Gamma=\operatorname{BiCay}(H,R,L,S)$ be a connected bi-Cayley graph over a finite abelian group $H$. If $\Gamma$ is edge transitive, then it is vertex transitive. If $\Gamma$ is half-arc-transitive, then $R\cup L$ is nonempty and has no involution, $|R|=|L|$ is even, $|S|>2$, and every vertex has degree at least six:
--
--   $$
--   \begin{aligned}
--   \Gamma\text{ edge transitive}&\Longrightarrow\Gamma\text{ vertex transitive},\\
--   \Gamma\text{ half-arc-transitive}&\Longrightarrow R\cup L\ne\varnothing,\ \operatorname{ord}(x)\ne2\ (x\in R\cup L),\\
--   &|R|=|L|\in2\mathbb N,\quad |S|>2,\quad\deg_\Gamma(v)\ge6\ (v\in V(\Gamma)).
--   \end{aligned}
--   $$
--
--   The result constrains the possible local structure of half-arc-transitive bi-Cayley graphs and excludes semisymmetric bi-Cayley graphs over abelian groups.
--
--   **Formalization Note** The first printed sentence omits “edge transitive” and is false for the connected generalized Petersen graph $GP(7,2)$. Proposition 4.1(b) proves the corrected sentence. The second sentence needs no correction because half-arc-transitivity includes edge transitivity.
-- source:
--   Conder, Zhou, Feng and Zhang, Edge-transitive bi-Cayley graphs, arXiv:1606.04625v1, p. 3, Proposition 1.3; corrected first sentence per p. 6, Proposition 4.1(b)

import Mathlib
import Definitions.Def_EdgeTransBiCayley_BiAbelian_Setting
open Pointwise

namespace EdgeTransBiCayley.BiAbelian

/-- Proposition 1.3, p. 3. The first sentence needs edge transitivity, as proved
in Proposition 4.1(b); the printed unrestricted sentence is false. -/
theorem proposition_1_3 {H : Type*} [CommGroup H] [Fintype H] [DecidableEq H]
    (D : BiCayData H) (hconn : D.graph.Connected) :
    (IsEdgeTransitive D.graph → IsVertexTransitive D.graph) ∧
    (IsHalfArcTransitive D.graph →
      (D.R ∪ D.L).Nonempty ∧
      (∀ x ∈ D.R ∪ D.L, orderOf x ≠ 2) ∧
      D.R.card = D.L.card ∧ Even D.R.card ∧
      2 < D.S.card ∧
      ∀ v, 6 ≤ D.graph.degree v) := by sorry
end EdgeTransBiCayley.BiAbelian
