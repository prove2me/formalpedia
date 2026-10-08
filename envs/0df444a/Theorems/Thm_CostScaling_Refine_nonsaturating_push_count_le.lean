-- Prove2me | Theorems.Thm_CostScaling_Refine_nonsaturating_push_count_le
-- name    : CostScaling.Refine.nonsaturating_push_count_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:27:06.478182+00:00
-- url     : https://prove2.me/theorems/a62adeb5-683e-4b49-9de6-61c802b19fa2
-- title:
--   Lemma 5.11 — at most 3n²(m + n) nonsaturating pushes
-- statement:
--   For any run of generic refine entered with a $2\varepsilon$-optimal circulation and $\varepsilon>0$, let $T$ count pushes for which the selected arc still has positive residual capacity after the push. With $n=|V|$ and $m=|E|$ ordered arcs,
--
--   $$
--   T\le 3n^2(m+n).
--   $$
--
--   This is the third component of the explicit operation bound.
--
--   **Formalization Note** Nonsaturation is tested in the successor state, and the $\varepsilon$ parameter is the value after the entry parameter is halved.
-- source:
--   Goldberg & Tarjan, MIT/LCS/TM-333 (July 1987), Lemma 5.11, p. 23; https://publications.csail.mit.edu/lcs/pubs/pdf/MIT-LCS-TM-333.pdf

import Mathlib
import Definitions.Def_CostScaling_Refine_Run

namespace CostScaling.Refine

/-- Lemma 5.11, pp. 23–24. -/
theorem nonsaturating_push_count_le {V : Type*} [Fintype V] [DecidableEq V]
    (N : Network V) (ε : ℝ) (hε : 0 < ε)
    (f₀ : V → V → ℝ) (p₀ : V → ℝ)
    (hcirc : CycleCanceling.MinMean.IsCirculation N f₀)
    (hentry : IsEpsOptimal N (2 * ε) f₀ p₀)
    (σ : ℕ → State V) (K : ℕ)
    (hrun : IsRun N ε f₀ p₀ σ K) :
    nonsaturatingPushCount N σ K ≤
      3 * Fintype.card V ^ 2 * (N.E.card + Fintype.card V) := by sorry

end CostScaling.Refine
