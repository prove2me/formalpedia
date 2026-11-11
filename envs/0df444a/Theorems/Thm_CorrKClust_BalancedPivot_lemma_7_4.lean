-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_lemma_7_4
-- name    : CorrKClust.BalancedPivot.lemma_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:06.27735+00:00
-- url     : https://prove2.me/theorems/619afaf6-87bc-44c1-87f9-230752a52dc8
-- title:
--   Lemma 7.4 — lower bound on optimal cost using PIVOT
-- statement:
--   For a finite graph $G$ and $k\ge1$, let $J_\sigma$ be the union of cliques whose sizes are the final PIVOT-cluster sizes under a uniform order $\sigma$. Then
--   $$\tfrac12\mathbb E_\sigma[s(J_\sigma)a(J_\sigma)]\le4\operatorname{OPT}_k(G).$$
--   The paper states this as an $\Omega$ lower bound. The displayed constants are those established at the end of its proof on p. 30. They relate random pivot-based clique parameters to a deterministic optimum, with zero product when there are at most k pivots.
--
--   Differences from the source:
--   - encoding: finite vertex set and unordered disagreements → Fintype V, SimpleGraph V, maps to labels, and unordered distinct Sym2 pairs; reason: decidable equality is classical data and no finite graph or clustering is excluded
--   - encoding: at most k possibly empty clusters → k > 0 and assignments V → Fin k; reason: positive k is required for an assignment on nonempty inputs and all unused labels remain legal
--   - encoding: uniform random arrival order → the finite average over all bijections Fin (card V) ≃ V; reason: there are exactly n! such bijections, each with equal weight
--   - generalization: Ω(E[s(Jσ)a(Jσ)]) ≤ Cost(OPT_k(I)) → (1/2) E[s(Jσ)a(Jσ)] ≤ 4 OPT_k(I); reason: the final display in the proof gives these explicit constants and implies the stated Ω form
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), Lemma 7.4 and its proof, p. 30, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/302.pdf

import Definitions.Def_CorrKClust_BalancedPivot_Analysis

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot

/-- Lemma 7.4, p. 30, with the explicit constants in its proof. -/
theorem lemma_7_4 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {k : ℕ} (hk : 0 < k) :
    (1 / 2 : ℝ) * average (fun σ : ArrivalOrder V =>
      (cliqueS (pivotSizes G σ) k : ℝ) * cliqueA (pivotSizes G σ) k) ≤ 4 * (optK G k : ℝ) := by sorry

end CorrKClust.BalancedPivot
