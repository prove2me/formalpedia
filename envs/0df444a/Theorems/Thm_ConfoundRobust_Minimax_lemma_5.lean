-- Prove2me | Theorems.Thm_ConfoundRobust_Minimax_lemma_5
-- name    : ConfoundRobust.Minimax.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:11:56.375788+00:00
-- url     : https://prove2.me/theorems/ac14eef8-fa31-40e5-bcb9-9ad639b3f4eb
-- title:
--   Lemma 5 (16), p. 41 — sup_S h − sup_S g ≤ sup_S (h − g)
-- statement:
--   Let $S$ be a nonempty set and $h, g : S \to \mathbb R$ functions whose values on $S$, and the values of $h - g$, are bounded above. Then
--   $$\sup_{y \in S} h(y) - \sup_{y \in S} g(y) \le \sup_{y \in S} \{h(y) - g(y)\}.$$
--
--   In the proof of Theorem 6 this inequality turns the difference of a sample and a population worst case into a supremum of differences, to which uniform-convergence bounds apply.
--
--   **Formalization Note** The page's proof takes maximizers of $h$, $g$ and $h - g$. Lean only assumes the three images bounded above, which is weaker and suffices; without boundedness of $h - g$ the real `sSup` of an unbounded set is $0$ and the inequality could fail.
-- source:
--   Kallus & Zhou, arXiv:1805.08593v3, Lemma 5, display (16), Appendix B.2, p. 41

import Mathlib
import Definitions.Def_ConfoundRobust_Minimax_Setting

open MeasureTheory

namespace ConfoundRobust.Minimax

theorem lemma_5 {α : Type*} (S : Set α) (h g : α → ℝ) (hS : S.Nonempty)
    (hh : BddAbove (h '' S)) (hg : BddAbove (g '' S))
    (hhg : BddAbove ((fun y => h y - g y) '' S)) :
    sSup (h '' S) - sSup (g '' S) ≤ sSup ((fun y => h y - g y) '' S) := by sorry

end ConfoundRobust.Minimax
