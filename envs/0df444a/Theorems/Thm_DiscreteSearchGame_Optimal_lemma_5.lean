-- Prove2me | Theorems.Thm_DiscreteSearchGame_Optimal_lemma_5
-- name    : DiscreteSearchGame.Optimal.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:53.905935+00:00
-- url     : https://prove2.me/theorems/7b86b8c7-9370-4254-ab80-96d15b05b617
-- title:
--   Lemma 5, p. 10 — for each optimal p*, G and G(ε) share value, p* and optimal search strategies for all small ε
-- statement:
--   Consider the search game $G$ and its set $\mathcal P^*$ of optimal hiding strategies. For any $p^*\in\mathcal P^*$ there exists $\epsilon_{p^*}\in(0,1/n]$ such that for every $\epsilon\in(0,\epsilon_{p^*})$:
--
--   1. $G$ and $G(\epsilon)$ have the same value;
--   2. $p^*$ is optimal in $G(\epsilon)$ as well as in $G$;
--   3. a search strategy is optimal in $G$ if and only if it is optimal in $G(\epsilon)$; in particular every optimal search strategy of $G(\epsilon)$ uses none of the pseudo-strategies $\zeta_i(\epsilon)$.
--
--   This reduces the existence of an optimal search strategy in $G$ to Lemma 4.
--
--   **Formalization Note.** Item 3 is stated in two parts: a mixed strategy $\eta$ of $G$ is optimal in $G$ iff its image under `Sum.inl` is optimal in $G(\epsilon)$; and every optimal strategy of $G(\epsilon)$ is supported on search sequences (`Sum.inl`), so it is a strategy of $G$. The second part is how the proof (p. 11, "and vice versa") reads the claim for strategies of $G(\epsilon)$ that are not strategies of $G$.
-- source:
--   Clarkson, Lin & Glazebrook, A Classical Search Game in Discrete Locations, arXiv:2103.09310v1, p. 10, Lemma 5 (proof pp. 10–11)

import Mathlib
import Definitions.Def_AllocationIndices_Jobs
import Definitions.Def_DiscreteSearchGame_Optimal_Model

open AllocationIndices Filter Topology

namespace DiscreteSearchGame.Optimal

/-- Lemma 5, p. 10: for an optimal hiding strategy `p*` there is `ε_{p*} ∈ (0, 1/n]` such that
for every `ε ∈ (0, ε_{p*})`, `G` and `G(ε)` have the same value, `p*` is optimal in `G(ε)`, a
search strategy of `G` is optimal in `G` iff it is optimal in `G(ε)`, and every optimal search
strategy of `G(ε)` uses no pseudo-strategy `ζᵢ(ε)`. -/
theorem lemma_5 {n : ℕ} (t q : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1)
    (p : Fin n → ℝ) (hp : IsOptimalHider t q p) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / (n : ℝ) ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      perturbedValue t q ε = gameValue t q ∧
      IsOptimalHiderPert t q ε p ∧
      (∀ η : PMF (ℕ → Fin n),
        IsOptimalSearcher t q η ↔ IsOptimalSearcherPert t q ε (η.map Sum.inl)) ∧
      (∀ μ : PMF (PerturbedStrategy n), IsOptimalSearcherPert t q ε μ →
        ∀ s ∈ μ.support, ∃ ξ, s = Sum.inl ξ) := by sorry

end DiscreteSearchGame.Optimal
