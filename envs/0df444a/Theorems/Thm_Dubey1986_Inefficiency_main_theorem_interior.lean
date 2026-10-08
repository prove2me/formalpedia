-- Prove2me | Theorems.Thm_Dubey1986_Inefficiency_main_theorem_interior
-- name    : Dubey1986.Inefficiency.main_theorem_interior
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:33:32.233577+00:00
-- url     : https://prove2.me/theorems/654c8668-79d4-4783-a373-65b85234f743
-- title:
--   p. 6, ¶2 — the Theorem for interior points: generically, interior N.E. are finite and none is efficient
-- statement:
--   Let $n\ge2$, $k(i)\ge1$, and let $V^i\supseteq S^i$ be open. There is an open dense set $U^*$ of $(U)^n$ such that for every $u\in U^*$:
--   1. the Nash equilibria $s$ of $u$ with every $s^i$ in the interior of $S^i$ are finite in number;
--   2. no Nash equilibrium of $u$ that is also efficient has all of its components $s^i$ in the interior of $S^i$.
--
--   This is the conclusion of the first part of the proof, "the proof of the theorem for $s\in\operatorname{Int}S^1\times\dots\times\operatorname{Int}S^n$". The boundary case (faces of the simplices and subgames) then gives the full Theorem.
-- source:
--   Dubey, Inefficiency of Nash Equilibria, IIASA WP-83-74 (July 1983), p. 6, second paragraph

import Mathlib
import Definitions.Def_Dubey1986_Inefficiency_Setting

namespace Dubey1986.Inefficiency

theorem main_theorem_interior {n : ℕ} (hn : 2 ≤ n) (k : Fin n → ℕ) (hk : ∀ i, 1 ≤ k i)
    (V : ∀ i, Set (Fin (k i) → ℝ)) (hVo : ∀ i, IsOpen (V i))
    (hSV : ∀ i, simplex (k i) ⊆ V i) :
    ∃ Ustar : Set (Fin n → Strat k → ℝ), IsOpenDense V Ustar ∧ ∀ u ∈ Ustar,
      {s | s ∈ NashSet u ∧ ∀ i, s i ∈ interior (simplex (k i))}.Finite ∧
      ∀ s ∈ NashSet u ∩ EffSet u, ¬ ∀ i, s i ∈ interior (simplex (k i)) := by sorry

end Dubey1986.Inefficiency
