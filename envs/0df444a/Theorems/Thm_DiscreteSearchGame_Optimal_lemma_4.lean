-- Prove2me | Theorems.Thm_DiscreteSearchGame_Optimal_lemma_4
-- name    : DiscreteSearchGame.Optimal.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:45.483067+00:00
-- url     : https://prove2.me/theorems/d88bd611-db4d-4076-9e11-d7df28fc8cb1
-- title:
--   Lemma 4, p. 10 — for ε ∈ (0, 1/n), G(ε) has an optimal search strategy mixing at most n search sequences
-- statement:
--   For any $\epsilon\in(0,1/n)$, the perturbed search game $G(\epsilon)$ has an optimal search strategy that is a mixture of at most $n$ of its pure search strategies, i.e. of at most $n$ elements of
--   $$\mathcal C(\epsilon)=\{\xi\in\mathcal C_p:\ p\in\mathcal P(\epsilon)\}\cup\{\zeta_i(\epsilon):i=1,\dots,n\}.$$
--   Here optimal means that the expected payoff is at most the value of $G(\epsilon)$ wherever the hider hides.
--
--   **Formalization Note.** A mixed strategy of $G(\epsilon)$ is a `PMF` on `(ℕ → Fin n) ⊕ Fin n` supported in $\mathcal C(\epsilon)$, `Sum.inr i` standing for $\zeta_i(\epsilon)$. "At most $n$" bounds the support by a finite set of cardinality at most $n$. The value of $G(\epsilon)$ is the hider's max-inf over the whole simplex, as for $G$.
-- source:
--   Clarkson, Lin & Glazebrook, A Classical Search Game in Discrete Locations, arXiv:2103.09310v1, p. 10, Lemma 4 (game G(ε) defined pp. 9–10, (7)–(8))

import Mathlib
import Definitions.Def_AllocationIndices_Jobs
import Definitions.Def_DiscreteSearchGame_Optimal_Model

open AllocationIndices Filter Topology

namespace DiscreteSearchGame.Optimal

/-- Lemma 4, p. 10: for `ε ∈ (0, 1/n)`, `G(ε)` has an optimal search strategy that mixes at most
`n` of its pure search strategies. -/
theorem lemma_4 {n : ℕ} (t q : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1)
    (ε : ℝ) (hε : 0 < ε) (hεn : ε < 1 / (n : ℝ)) :
    ∃ μ : PMF (PerturbedStrategy n), IsOptimalSearcherPert t q ε μ ∧
      ∃ s : Finset (PerturbedStrategy n), s.card ≤ n ∧
        (↑s : Set (PerturbedStrategy n)) ⊆ perturbedAllowed t q ε ∧ μ.support ⊆ ↑s := by sorry

end DiscreteSearchGame.Optimal
