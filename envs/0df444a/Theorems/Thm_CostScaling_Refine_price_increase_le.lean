-- Prove2me | Theorems.Thm_CostScaling_Refine_price_increase_le
-- name    : CostScaling.Refine.price_increase_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:26:35.87619+00:00
-- url     : https://prove2.me/theorems/b01b0c45-6b02-4bbc-a41c-c4c1c8b1dcb2
-- title:
--   Lemma 5.8 — price increase at most 3nε
-- statement:
--   Let $n=|V|$, let $\varepsilon>0$, and enter refine with a circulation $f_0$ that is $2\varepsilon$-optimal with respect to $p_0$. During any run of the generic subroutine, every vertex price is bounded above by its entry value plus $3n\varepsilon$:
--
--   $$
--   p_k(v)\le p_0(v)+3n\varepsilon\qquad(0\le k\le K,\ v\in V).
--   $$
--
--   This price bound limits how often relabel can occur and thus supports the operation counts.
--
--   **Formalization Note** The source's $\varepsilon$ is the parameter after halving. The entry circulation and its $2\varepsilon$-optimality are explicit hypotheses.
-- source:
--   Goldberg & Tarjan, MIT/LCS/TM-333 (July 1987), Lemma 5.8, p. 22; https://publications.csail.mit.edu/lcs/pubs/pdf/MIT-LCS-TM-333.pdf

import Mathlib
import Definitions.Def_CostScaling_Refine_Run

namespace CostScaling.Refine

/-- Lemma 5.8, p. 22: the bound uses the error parameter after halving. -/
theorem price_increase_le {V : Type*} [Fintype V] [DecidableEq V]
    (N : Network V) (ε : ℝ) (hε : 0 < ε)
    (f₀ : V → V → ℝ) (p₀ : V → ℝ)
    (hcirc : CycleCanceling.MinMean.IsCirculation N f₀)
    (hentry : IsEpsOptimal N (2 * ε) f₀ p₀)
    (σ : ℕ → State V) (K : ℕ)
    (hrun : IsRun N ε f₀ p₀ σ K) :
    ∀ k ≤ K, ∀ v, (σ k).p v ≤ p₀ v + 3 * (Fintype.card V : ℝ) * ε := by sorry

end CostScaling.Refine
