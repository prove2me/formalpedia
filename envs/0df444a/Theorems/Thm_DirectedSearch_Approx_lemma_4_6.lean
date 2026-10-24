-- Prove2me | Theorems.Thm_DirectedSearch_Approx_lemma_4_6
-- name    : DirectedSearch.Approx.lemma_4_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:13.790617+00:00
-- url     : https://prove2.me/theorems/bf41cf1c-bacf-4505-95a8-4ed90796fb7d
-- title:
--   Lemma 4.6, p. 23 — the generalized assignment LP has an optimal solution with forest support
-- statement:
--   Let $\mathcal M,\mathcal W$ be finite, let $\rho_{mw}\in\mathbb R$ be arbitrary weights and $\alpha_m,\alpha_w\ge0$ real capacities. Consider the generalized assignment problem
--   $$\max\ \sum_{m\in\mathcal M}\sum_{w\in\mathcal W}\rho_{mw}\beta_{mw}\quad\text{s.t.}\quad\beta\ge0,\quad\sum_w\beta_{mw}\le\alpha_m\ \ \forall m,\quad \sum_m\beta_{mw}\le\alpha_w\ \ \forall w.$$
--   There is an optimal solution $\beta^*$ such that the graph on $\Theta=\mathcal M\sqcup\mathcal W$ with edge set $\{(m,w):\beta^*_{mw}>0\}$ is a forest.
--
--   This is Step (1) of the approximation: an optimal first-best solution whose positive variables form a forest.
--
--   **Formalization Note.** $\beta\ge0$ (implicit in the paper) and nonnegative capacities are added; with a negative capacity no nonnegative $\beta$ is feasible. In the application the capacities are arrival rates. Optimality is stated against every feasible $\beta$.
-- source:
--   Immorlica, Lucier, Manshadi, Wei, Designing Approximately Optimal Search on Matching Platforms, arXiv:2102.09017v2, p. 23, Lemma 4.6 (citing Lenstra et al. 1990, Chakrabarty and Goel 2010, Banerjee et al. 2017)

import Mathlib
import Definitions.Def_DirectedSearch_Approx_Graphs

namespace DirectedSearch.Approx
theorem lemma_4_6 {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (ρ : M → W → ℝ) (αM : M → ℝ) (αW : W → ℝ) (hαM : ∀ m, 0 ≤ αM m) (hαW : ∀ w, 0 ≤ αW w) :
    ∃ βstar : M → W → ℝ,
      ((∀ m w, 0 ≤ βstar m w) ∧ (∀ m, ∑ w, βstar m w ≤ αM m) ∧ (∀ w, ∑ m, βstar m w ≤ αW w)) ∧
      (∀ β : M → W → ℝ, (∀ m w, 0 ≤ β m w) → (∀ m, ∑ w, β m w ≤ αM m) →
        (∀ w, ∑ m, β m w ≤ αW w) → ∑ m, ∑ w, ρ m w * β m w ≤ ∑ m, ∑ w, ρ m w * βstar m w) ∧
      (supportGraph βstar).IsAcyclic := by sorry
end DirectedSearch.Approx
