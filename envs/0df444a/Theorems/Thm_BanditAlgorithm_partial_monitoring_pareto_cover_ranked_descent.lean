-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_pareto_cover_ranked_descent
-- name    : BanditAlgorithm.partial_monitoring_pareto_cover_ranked_descent
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T18:46:57.040172+00:00
-- url     : https://prove2.me/theorems/f9bd6141-c9d8-40f4-b01d-478bc73f7b52
-- title:
--   Ranked non-increasing descent in a Pareto-cell cover
-- statement:
--   For every finite partial-monitoring game, one can select a nonempty collection $S$ of duplicate-free Pareto representatives whose cells cover the outcome simplex, so every finite outcome sequence has a hindsight-optimal action in $S$. For each mixed outcome $\lambda$, there are a root and a natural-number rank such that every non-root $b\in S$ has a neighbouring successor $c\in S$ whose $\lambda$-expected loss does not increase and whose rank strictly decreases.
--
--   The rank records an acyclic orientation of the non-increasing in-tree. Unlike the strict-interior argument, this formulation remains correct when $\lambda$ lies on cell boundaries and several actions tie.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Cambridge University Press (2020), Lemma 37.7 p. 484, Exercise 37.10 p. 509, and Lemma 37.21 pp. 501–502, especially the finite-subsequence boundary argument. https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringGame

open scoped BigOperators

theorem BanditAlgorithm.partial_monitoring_pareto_cover_ranked_descent
    {k d : ℕ} {𝕊 : Type*}
    (G : PartialMonitoringGame k d 𝕊) (hk : 2 ≤ k) (hd : 0 < d) :
    ∃ S : Finset (Fin k),
      S.Nonempty ∧
      (∀ (n : ℕ) (i : Fin n → Fin d), ∃ b ∈ S, ∀ a : Fin k,
        ∑ t, G.L b (i t) ≤ ∑ t, G.L a (i t)) ∧
      ∀ lam : Fin d → ℝ, lam ∈ stdSimplex ℝ (Fin d) →
        ∃ root ∈ S, ∃ rank : Fin k → ℕ,
          ∀ b ∈ S, b ≠ root →
            ∃ c ∈ S, NeighbouringActions G b c ∧
              ∑ i : Fin d, G.L c i * lam i ≤
                ∑ i : Fin d, G.L b i * lam i ∧
              rank c < rank b := by
  sorry
