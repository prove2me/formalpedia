-- Prove2me | Theorems.Thm_DantzigSimplex_Technique_section_1_termination
-- name    : DantzigSimplex.Technique.section_1_termination
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:22:10.834834+00:00
-- url     : https://prove2.me/theorems/a94c5c58-dbb0-431c-9184-69b726f70a7c
-- title:
--   Section 1, conditions (17)–(18) — Phase II termination
-- statement:
--   Assume $1\le m\le n$ and Dantzig's nondegeneracy condition. For the strictly positive $m$-column Phase II states and the pivots determined by (11), (13), and (16), there is no infinite sequence of pivots. At any state with no admissible pivot, either some improving column $j$ has $x_{ij}\le0$ for every basic index $i$, as in (17), or $c_j\le z_j$ for every column $j$, as in (18):
--
--   $$
--   \bigl(\exists j:\ c_j>z_j\ \land\ \forall i\in B,\ x_{ij}\le0\bigr)
--   \quad\lor\quad
--   \bigl(\forall j,\ c_j\le z_j\bigr).
--   $$
--
--   **Formalization Note** The entering index in (17) must also satisfy (11); otherwise a basic column could make the condition misleading.
-- source:
--   Dantzig, Maximization of a Linear Function of Variables Subject to Linear Inequalities, in Koopmans (ed.), Activity Analysis of Production and Allocation, Wiley 1951, Ch. XXI, pp. 342–343, Section 1, conditions (17)–(18)

import Mathlib
import Definitions.Def_DantzigSimplex_Technique_Process

namespace DantzigSimplex.Technique

/-- Section 1, pp. 342--343: no basis can recur and terminal states satisfy (17) or (18). -/
theorem section_1_termination {m n : ℕ} (p : Problem m n)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hnd : p.Nondegenerate) :
    (¬ ∃ f : ℕ → PhaseIIState p, ∀ k, PhaseIIStep (f k) (f (k + 1))) ∧
    (∀ s : PhaseIIState p,
      (¬ ∃ t : PhaseIIState p, PhaseIIStep s t) →
      (∃ j : Fin n, p.cost j > s.frame.z j ∧
        (∀ i ∈ s.frame.B, s.frame.x i j ≤ 0)) ∨
      (∀ j, p.cost j ≤ s.frame.z j)) := by sorry

end DantzigSimplex.Technique
