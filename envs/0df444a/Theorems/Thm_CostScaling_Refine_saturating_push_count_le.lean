-- Prove2me | Theorems.Thm_CostScaling_Refine_saturating_push_count_le
-- name    : CostScaling.Refine.saturating_push_count_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:26:51.226531+00:00
-- url     : https://prove2.me/theorems/383a22cb-b493-4640-96d8-cd71e0b6b273
-- title:
--   Lemma 5.10 — at most 3nm saturating pushes
-- statement:
--   For any run of generic refine entered with a $2\varepsilon$-optimal circulation and $\varepsilon>0$, let $S$ count pushes for which the selected arc is saturated after the push. With $n=|V|$ and $m=|E|$ ordered arcs,
--
--   $$
--   S\le 3nm.
--   $$
--
--   This is the second component of the explicit operation bound.
--
--   **Formalization Note** Saturation is tested in the successor state. The $m$ of this report counts directed arcs, including both orientations of each edge.
-- source:
--   Goldberg & Tarjan, MIT/LCS/TM-333 (July 1987), Lemma 5.10, p. 23; https://publications.csail.mit.edu/lcs/pubs/pdf/MIT-LCS-TM-333.pdf

import Mathlib
import Definitions.Def_CostScaling_Refine_Run

namespace CostScaling.Refine

/-- Lemma 5.10, p. 23. The paper counts ordered arcs of `E`. -/
theorem saturating_push_count_le {V : Type*} [Fintype V] [DecidableEq V]
    (N : Network V) (ε : ℝ) (hε : 0 < ε)
    (f₀ : V → V → ℝ) (p₀ : V → ℝ)
    (hcirc : CycleCanceling.MinMean.IsCirculation N f₀)
    (hentry : IsEpsOptimal N (2 * ε) f₀ p₀)
    (σ : ℕ → State V) (K : ℕ)
    (hrun : IsRun N ε f₀ p₀ σ K) :
    saturatingPushCount N σ K ≤ 3 * Fintype.card V * N.E.card := by sorry

end CostScaling.Refine
