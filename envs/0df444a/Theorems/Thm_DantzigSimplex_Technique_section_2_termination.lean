-- Prove2me | Theorems.Thm_DantzigSimplex_Technique_section_2_termination
-- name    : DantzigSimplex.Technique.section_2_termination
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:22:00.489733+00:00
-- url     : https://prove2.me/theorems/74f1669e-a48c-40fb-96a9-4c3a76b915f0
-- title:
--   Section 2, conditions (44)–(45) — Phase I termination
-- statement:
--   Assume $1\le m\le n$, every $m$ among $P_0,P_1,\ldots,P_n$ are independent, and the fixed reference point $G$ is in general position with $P_0$ and the columns. Fix an initial Phase I state with positive basic weights. Then there is no infinite sequence of the Phase I ratio-test pivots (36)–(41). Every Phase I state admitting no further Phase I pivot has one of two outcomes:
--
--   1. $y_{0j}\le0$ for all $j$, and the original linear program has no feasible solution.
--   2. Some $j$ has $y_{0j}>0$ and $y_{ij}\le0$ for all current basic indices $i$; the weights from (39) form a strictly positive $m$-column Phase II state.
--
--   This gives the complete termination and hand-off assertion of Section 2. **Formalization Note** The general-position hypothesis is additional to the printed assumptions: it rules out tied ratio minima that otherwise leave a zero weight and invalidate the stated increase of $\rho$. The printed condition (45) ranges over $m$ indices, but the Phase I basis has $m-1$; the quantifier is over the current basis.
-- source:
--   Dantzig, Maximization of a Linear Function of Variables Subject to Linear Inequalities, in Koopmans (ed.), Activity Analysis of Production and Allocation, Wiley 1951, Ch. XXI, pp. 346–347, Section 2, Eqs. (36)–(45)

import Mathlib
import Definitions.Def_DantzigSimplex_Technique_Process

namespace DantzigSimplex.Technique

/-- Section 2, pp. 346--347: Phase I has no infinite pivot run and terminates in (44) or (45). -/
theorem section_2_termination {m n : ℕ} (p : Problem m n)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hnd : p.Nondegenerate)
    (G : Fin m → ℝ) (hgp : GeneralPosition p G)
    (initial : PhaseIState p G) :
    (¬ ∃ f : ℕ → PhaseIState p G, ∀ k, PhaseIStep (f k) (f (k + 1))) ∧
    (∀ s : PhaseIState p G,
      (¬ ∃ t : PhaseIState p G, PhaseIStep s t) →
      ((∀ j, s.frame.y0 j ≤ 0) ∧ (∀ w, ¬ p.Feasible w)) ∨
      (∃ j : Fin n, 0 < s.frame.y0 j ∧
        (∀ i ∈ s.frame.S, s.frame.y i j ≤ 0) ∧
        ∃ t : PhaseIIState p, HandOff s t)) := by sorry

end DantzigSimplex.Technique
