-- Prove2me | Theorems.Thm_FloydAlgorithms_ShortestPath_algorithm97_eq_top_of_no_path
-- name    : FloydAlgorithms.ShortestPath.algorithm97_eq_top_of_no_path
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:25:43.403189+00:00
-- url     : https://prove2.me/theorems/6eb6e675-53fe-40c8-bfdb-9be6ef3676a9
-- title:
--   Algorithm 97, comment — no path leaves the final entry at infinity
-- statement:
--   Let $w$ be any matrix of direct-link lengths, with $\infty$ for a missing link. If there is no finite-length path from point $i$ to point $j$, then Algorithm 97 leaves the final entry at infinity:
--
--   $$
--   \neg\exists p:i\leadsto j\text{ with }\ell_w(p)<\infty
--   \quad\Longrightarrow\quad
--   \operatorname{shortestPath}(w)(i,j)=\infty.
--   $$
--
--   This is the last sentence of Algorithm 97's comment, and it isolates the behavior on unreachable pairs.
--
--   **Formalization Note** Paths have at least one link, including when $i=j$. No restriction on link signs or negative cycles is imposed, because the absence of a path alone ensures this conclusion. The printed `₁₀10` is represented by `⊤ : WithTop ℝ`.
-- source:
--   Floyd, Algorithm 97: Shortest Path, Communications of the ACM 5(6) (1962), p. 345, comment, fourth sentence; https://doi.org/10.1145/367766.368168

import Mathlib
import Definitions.Def_FloydAlgorithms_ShortestPath_Network
import Definitions.Def_FloydAlgorithms_ShortestPath_Algorithm97

namespace FloydAlgorithms.ShortestPath

/-- Algorithm 97, comment, fourth sentence, p. 345: no path leaves the
final entry at infinity. No sign condition is needed here. -/
theorem algorithm97_eq_top_of_no_path {n : ℕ} (w : LengthMatrix n)
    (i j : Fin n)
    (h : ¬ ∃ (L : ℕ) (p : Fin (L + 1) → Fin n),
      IsPath i j L p ∧ pathLength w p ≠ ⊤) :
    algorithm97 w i j = ⊤ := by sorry

end FloydAlgorithms.ShortestPath
