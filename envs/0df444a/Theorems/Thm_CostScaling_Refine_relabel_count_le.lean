-- Prove2me | Theorems.Thm_CostScaling_Refine_relabel_count_le
-- name    : CostScaling.Refine.relabel_count_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:26:36.314363+00:00
-- url     : https://prove2.me/theorems/7180911c-0723-48e5-86ba-31a52624c1c2
-- title:
--   Lemma 5.9 — at most 3n(n − 1) relabelings
-- statement:
--   For any run of generic refine entered with a $2\varepsilon$-optimal circulation and $\varepsilon>0$, let $R$ be the number of relabel operations among its $K$ updates. If $n=|V|$, then
--
--   $$
--   R\le 3n(n-1).
--   $$
--
--   This is the first component of the explicit bound on the number of update operations.
--
--   **Formalization Note** $R$ counts actual relabel steps in a run from Figure 4's initialization. The parameter $\varepsilon$ is the value after halving. The natural subtraction $n-1$ is zero at $n=0$, where no relabel step is possible.
-- source:
--   Goldberg & Tarjan, MIT/LCS/TM-333 (July 1987), Lemma 5.9, p. 23; https://publications.csail.mit.edu/lcs/pubs/pdf/MIT-LCS-TM-333.pdf

import Mathlib
import Definitions.Def_CostScaling_Refine_Run

namespace CostScaling.Refine

/-- Lemma 5.9, p. 23. -/
theorem relabel_count_le {V : Type*} [Fintype V] [DecidableEq V]
    (N : Network V) (ε : ℝ) (hε : 0 < ε)
    (f₀ : V → V → ℝ) (p₀ : V → ℝ)
    (hcirc : CycleCanceling.MinMean.IsCirculation N f₀)
    (hentry : IsEpsOptimal N (2 * ε) f₀ p₀)
    (σ : ℕ → State V) (K : ℕ)
    (hrun : IsRun N ε f₀ p₀ σ K) :
    relabelCount N ε σ K ≤ 3 * Fintype.card V * (Fintype.card V - 1) := by sorry

end CostScaling.Refine
