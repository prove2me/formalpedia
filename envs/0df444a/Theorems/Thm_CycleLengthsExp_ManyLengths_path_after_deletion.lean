-- Prove2me | Theorems.Thm_CycleLengthsExp_ManyLengths_path_after_deletion
-- name    : CycleLengthsExp.ManyLengths.path_after_deletion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:33.992744+00:00
-- url     : https://prove2.me/theorems/6e6aa419-221a-4cd6-ad30-5fc6855cf494
-- title:
--   Theorem 2 proof — a long path after deleting ⌊αn/4⌋ vertices
-- statement:
--   Let $0<\alpha\le1$, and let $G$ be an $\alpha$-expander on $n>0$ vertices. If $S$ is any vertex set with $|S|=\lfloor\alpha n/4\rfloor$, then $G\setminus S$ has a simple path with exactly
--   $$\left\lceil\frac{\alpha n}{4}\right\rceil-1$$
--   edges. In other words, every vertex of the path lies outside $S$.
--
--   The path supplies the large set of vertices along which the later cycle construction varies its length.
--
--   **Formalization Note** The page obtains $S$ as the vertices of a breadth-first-search tree, but its displayed expansion estimate uses only $|S|$. This item states the resulting path claim for every set of that size. The additional $n>0$ makes a starting vertex available. The paper cites “Lemma 2.4” here; the long-path statement is Lemma 2.5.
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 13, proof of Theorem 2, paragraph beginning 'Run the BFS algorithm'

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

namespace CycleLengthsExp.ManyLengths

/-- The path in `G \ T` in the proof of Theorem 2, p. 13. -/
theorem path_after_deletion (n : ℕ) (hn : 0 < n) (α : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (G : SimpleGraph (Fin n))
    (hG : CycleLengthsExp.WellSpread.IsAlphaExpander α G) (S : Set (Fin n))
    (hS : S.ncard = Nat.floor (α * (n : ℝ) / 4)) :
    ∃ (u v : Fin n) (p : G.Walk u v),
      p.IsPath ∧ p.length = Nat.ceil (α * (n : ℝ) / 4) - 1 ∧
      ∀ w ∈ p.support, w ∉ S := by sorry

end CycleLengthsExp.ManyLengths
