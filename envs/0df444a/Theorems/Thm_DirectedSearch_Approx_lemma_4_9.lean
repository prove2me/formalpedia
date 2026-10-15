-- Prove2me | Theorems.Thm_DirectedSearch_Approx_lemma_4_9
-- name    : DirectedSearch.Approx.lemma_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:11.902099+00:00
-- url     : https://prove2.me/theorems/c0e8d4b0-2c19-458c-aa02-b314688cd05e
-- title:
--   Lemma 4.9, p. 24 — in a star-shaped market the first best fills the w's in decreasing order of ρ_mw
-- statement:
--   Consider a market satisfying the standing assumptions in which $\mathcal M=\{m\}$. There is an optimal solution $\beta^*$ of LP (7) (a first-best solution, by Proposition 4.4) and distinct types $w_1,\dots,w_n\in\mathcal W$ such that
--
--   1. $\rho_{mw_1}\ge\rho_{mw_2}\ge\cdots\ge\rho_{mw_n}$;
--   2. $\beta^*_{mw_i}=\alpha_{w_i}$ for all $i<n$;
--   3. $\beta^*_{mw}=0$ for $w\notin\{w_1,\dots,w_n\}$.
--
--   In a star-shaped market LP (7) is a fractional knapsack, and this lemma records the shape of its greedy solution.
--
--   **Formalization Note.** The list is `ws : Fin n → W`, injective and indexed from 0, so the paper's "$i<n$" (1-based) is `i.val + 1 < n`; $n=0$ is allowed. The ordering is stated for all pairs $i\le j$.
-- source:
--   Immorlica, Lucier, Manshadi, Wei, Designing Approximately Optimal Search on Matching Platforms, arXiv:2102.09017v2, p. 24, Lemma 4.9

import Mathlib
import Definitions.Def_DirectedSearch_Approx_Setting

namespace DirectedSearch.Approx
theorem lemma_4_9 {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mk : Market M W) (hmk : mk.Standing) (m : M) (hM : ∀ m' : M, m' = m) :
    ∃ βstar : M → W → ℝ, LPFeasible mk βstar ∧
      (∀ β, LPFeasible mk β → lpObj mk β ≤ lpObj mk βstar) ∧
      ∃ (n : ℕ) (ws : Fin n → W), Function.Injective ws ∧
        (∀ i j : Fin n, i ≤ j → rho mk m (ws j) ≤ rho mk m (ws i)) ∧
        (∀ i : Fin n, i.val + 1 < n → βstar m (ws i) = mk.αW (ws i)) ∧
        (∀ w, w ∉ Set.range ws → βstar m w = 0) := by sorry
end DirectedSearch.Approx
