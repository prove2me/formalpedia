-- Prove2me | Theorems.Thm_CostScaling_Refine_terminated_refine_correct
-- name    : CostScaling.Refine.terminated_refine_correct
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:26:31.025278+00:00
-- url     : https://prove2.me/theorems/67cbd933-2757-4577-9322-546cdc1c6e3b
-- title:
--   Theorem 5.4 — terminated refine returns an ε-optimal circulation
-- statement:
--   Let $f_0$ be a circulation that is $2\varepsilon$-optimal with respect to prices $p_0$, with $\varepsilon>0$. Start generic refine by halving the input error parameter and saturating all arcs of negative reduced cost. Let $\sigma_0,\ldots,\sigma_K$ be any resulting sequence of applicable push and relabel operations. If no operation is applicable in $\sigma_K$, then its pseudoflow $f_K$ is a circulation and remains $\varepsilon$-optimal with respect to its final prices $p_K$:
--
--   $$
--   \operatorname{Terminated}(\sigma_K)\quad\Longrightarrow\quad f_K\text{ is a circulation and }c_{p_K}(v,w)\ge-\varepsilon\text{ for every residual arc.}
--   $$
--
--   This is the partial correctness result for the generic subroutine; the update counts separately establish finite termination.
--
--   **Formalization Note** “Terminated” is the literal negation of Figure 4's update guard. The parameter $\varepsilon$ here is the new error parameter after Figure 4 halves the input $2\varepsilon$.
-- source:
--   Goldberg & Tarjan, MIT/LCS/TM-333 (July 1987), Theorem 5.4, p. 21; https://publications.csail.mit.edu/lcs/pubs/pdf/MIT-LCS-TM-333.pdf

import Mathlib
import Definitions.Def_CostScaling_Refine_Run

namespace CostScaling.Refine

/-- Theorem 5.4, p. 21, including the entry contract of refine. -/
theorem terminated_refine_correct {V : Type*} [Fintype V] [DecidableEq V]
    (N : Network V) (ε : ℝ) (hε : 0 < ε)
    (f₀ : V → V → ℝ) (p₀ : V → ℝ)
    (hcirc : CycleCanceling.MinMean.IsCirculation N f₀)
    (hentry : IsEpsOptimal N (2 * ε) f₀ p₀)
    (σ : ℕ → State V) (K : ℕ)
    (hrun : IsRun N ε f₀ p₀ σ K)
    (hterm : Terminated N (σ K)) :
    CycleCanceling.MinMean.IsCirculation N (σ K).f ∧
      IsEpsOptimal N ε (σ K).f (σ K).p := by sorry

end CostScaling.Refine
