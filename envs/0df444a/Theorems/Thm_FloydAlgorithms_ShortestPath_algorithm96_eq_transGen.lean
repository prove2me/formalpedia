-- Prove2me | Theorems.Thm_FloydAlgorithms_ShortestPath_algorithm96_eq_transGen
-- name    : FloydAlgorithms.ShortestPath.algorithm96_eq_transGen
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:08:49.984961+00:00
-- url     : https://prove2.me/theorems/a6bf7012-9edb-498d-abc6-0c75ab9d4b1e
-- title:
--   Algorithm 96, comment — the final matrix records ancestor chains
-- statement:
--   Let $b(i,j)$ initially say whether individual $i$ is a parent of individual $j$. Run Floyd's Algorithm 96 on this Boolean matrix. For every pair $(i,j)$, the final entry is true exactly when the initial relation contains a chain of one or more parent links from $i$ to $j$:
--
--   $$
--   \operatorname{ancestor}(b)(i,j)=\mathrm{true}
--   \quad\Longleftrightarrow\quad
--   i\mathrel{b^+}j.
--   $$
--
--   Here $b^+$ denotes transitive closure without reflexive links added. This result records reachability using the same loop pattern as the shortest-path procedure.
--
--   **Formalization Note** A parent counts as an ancestor through a chain of length one. A diagonal entry is true exactly when a positive-length chain returns to that point. The paper's “is true if” is read as an equivalence in light of its following “That is” sentence.
-- source:
--   Floyd, Algorithm 96: Ancestor, Communications of the ACM 5(6) (1962), pp. 344–345, comment, first through fourth sentences; https://doi.org/10.1145/367766.368168

import Mathlib
import Definitions.Def_FloydAlgorithms_ShortestPath_Algorithm96

namespace FloydAlgorithms.ShortestPath

/-- Algorithm 96, comment, pp. 344–345: the final Boolean matrix records
chains of one or more initially true parent links. -/
theorem algorithm96_eq_transGen {n : ℕ} (b : Fin n → Fin n → Bool)
    (i j : Fin n) :
    algorithm96 b i j = true ↔ Relation.TransGen (fun a c => b a c = true) i j := by sorry

end FloydAlgorithms.ShortestPath
