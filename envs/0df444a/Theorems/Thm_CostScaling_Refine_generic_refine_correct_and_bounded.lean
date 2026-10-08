-- Prove2me | Theorems.Thm_CostScaling_Refine_generic_refine_correct_and_bounded
-- name    : CostScaling.Refine.generic_refine_correct_and_bounded
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:26:51.117961+00:00
-- url     : https://prove2.me/theorems/4179693a-9e2d-4bac-b8a1-01392359e5ff
-- title:
--   Generic refine terminates within an explicit update bound at an ε-optimal circulation
-- statement:
--   Let $N$ be a finite symmetric circulation network with $n$ vertices and $m$ ordered arcs. Enter generic refine with $\varepsilon>0$, a circulation $f_0$, and prices $p_0$ for which $f_0$ is $2\varepsilon$-optimal. Start from Figure 4's initialized pseudoflow and take any $K$ applicable push or relabel steps, in any order. Then:
--
--   $$
--   K\le 3n(n-1)+3nm+3n^2(m+n).
--   $$
--
--   If the last state still has an active vertex, a further push or relabel step exists. If no operation applies there, its pseudoflow is a circulation and is $\varepsilon$-optimal with respect to its final prices. Consequently, every choice of applicable operations stops within the displayed bound at an $\varepsilon$-optimal circulation.
--
--   The result gathers the progress and correctness statements of Section 5 and the explicit bounds of Lemmas 5.9–5.11. It is an update count, not a RAM-model running time.
--
--   **Formalization Note** The formal parameter $\varepsilon$ is the error after Figure 4 halves the input $2\varepsilon$; $m$ counts ordered arcs. Termination uses Figure 4's loop guard, and a relabel successor requires an attained minimum over a nonempty residual set.
-- source:
--   Goldberg & Tarjan, MIT/LCS/TM-333 (July 1987), Theorem 5.4 and Lemmas 5.1, 5.9–5.11, p. 24; https://publications.csail.mit.edu/lcs/pubs/pdf/MIT-LCS-TM-333.pdf

import Mathlib
import Definitions.Def_CostScaling_Refine_Run

namespace CostScaling.Refine

/-- Theorem 5.4 and Lemmas 5.1, 5.9–5.11, with the paper's constants. -/
theorem generic_refine_correct_and_bounded {V : Type*} [Fintype V] [DecidableEq V]
    (N : Network V) (ε : ℝ) (hε : 0 < ε)
    (f₀ : V → V → ℝ) (p₀ : V → ℝ)
    (hcirc : CycleCanceling.MinMean.IsCirculation N f₀)
    (hentry : IsEpsOptimal N (2 * ε) f₀ p₀)
    (σ : ℕ → State V) (K : ℕ)
    (hrun : IsRun N ε f₀ p₀ σ K) :
    K ≤ 3 * Fintype.card V * (Fintype.card V - 1) +
        3 * Fintype.card V * N.E.card +
        3 * Fintype.card V ^ 2 * (N.E.card + Fintype.card V) ∧
    (∀ v, IsActive N (σ K).f v → ∃ t, IsStep N ε (σ K) t) ∧
    (Terminated N (σ K) →
      CycleCanceling.MinMean.IsCirculation N (σ K).f ∧
      IsEpsOptimal N ε (σ K).f (σ K).p) := by sorry

end CostScaling.Refine
