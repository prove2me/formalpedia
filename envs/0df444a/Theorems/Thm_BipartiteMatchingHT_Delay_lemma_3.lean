-- Prove2me | Theorems.Thm_BipartiteMatchingHT_Delay_lemma_3
-- name    : BipartiteMatchingHT.Delay.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T19:14:28.15627+00:00
-- url     : https://prove2.me/theorems/a06c8cae-e712-4fed-b644-428e85a47e03
-- title:
--   Lemma 3 — four resource-pooling properties (as printed)
-- statement:
--   Let $M$ be a heavy-traffic admissible matching and let $\widetilde M$ denote its residual matrix. All four printed properties hold:
--   1. Each component $(\mathcal C_k,\mathcal S_k)$ satisfies $\widetilde\lambda_{\mathcal C_k}=\mu_{\mathcal S_k}$.
--   2. Every strict server subset $A\subsetneq\mathcal S_k$, including the empty set, satisfies $U_A(\widetilde M)\subsetneq\mathcal C_k$ and $\widetilde\lambda_{U_A(\widetilde M)}<\mu_A$. Also $U_A(M)\subseteq U_A(\widetilde M)$ and $\widetilde\lambda_{U_A(M)}<\mu_A$.
--   3. For every topological order and every prefix of length $1\le r\le K$, the residual exclusively served customer set of its server union equals its customer union.
--   4. For that prefix server set $S_r$ and every $0<\rho<1$, $\Delta_\rho(S_r;M)=(1-\rho)\mu_{S_r}$.
--
--   The empty-subset assertion in part 2 is false as printed; the mission preserves it for possible disproof. The concrete one-server counterexample is recorded in INSIGHTS.yaml and is not replaced by a corrected milestone.
--
--   Differences from the source:
--   - encoding: classes and servers indexed from 1; binary matrix and arbitrary rewards → Fin n and Fin m indexed from 0; Boolean compatibility; omit rewards; reason: reindexing preserves all instances and rewards do not affect queue dynamics or delays
--   - encoding: independent Poisson arrivals and exponential services under FCFS-ALIS → a finite-mark Poisson event chain with null idle-server events and explicit ordered-list updates; reason: constant-rate uniformization gives the same countable-state queue; no finite queue cap or rate restriction is imposed
--   - encoding: the limiting family of operationally stable matchings → existence of a supported invariant probability vector for every real load sufficiently close to 1 from below; reason: stationarity is invariant under constant-rate uniformization; the limiting family is interpreted as eventual membership, without assuming any slack or delay theorem
--   - encoding: flows summed only on compatible edges and limiting maximum flows → flows are zero off compatible edges; residual support uses all saturated nominal feasible flows; reason: zero extension preserves the objective, and saturation is the equivalent feasibility test in Remark 3 and equation (6)
--   - encoding: numbered maximal connected residual components and their permutations → connected-component quotient and bijections from Fin K to that quotient; reason: enumerates the same components and each reversed topological order exactly once, without choosing an artificial labeling
--   - encoding: slack identity within the load family → identity for every real rho in (0,1); reason: makes the standing load domain explicit; the empty strict subset in part (ii) remains included
-- source:
--   Afèche, Caldentey and Gupta, On the Optimal Design of a Bipartite Matching Queueing System, Operations Research (catalog 2021), https://doi.org/10.1287/opre.2020.2027; acquired artifact dated November 3, 2019; citation_basis published; Lemma 3, printed/PDF p. 15

import Definitions.Def_BipartiteMatchingHT_Delay_Aggregates

open scoped BigOperators ENNReal
open Filter Topology

namespace BipartiteMatchingHT.Delay

theorem lemma_3
    {n m : ℕ} (D : BipartiteMatchingHT.Delay.Model n m)
    (hD : BipartiteMatchingHT.Delay.Admissible D) :
    (∀ k : BipartiteMatchingHT.Delay.Component D,
      D.demand (BipartiteMatchingHT.Delay.componentClasses D k) =
        D.capacity (BipartiteMatchingHT.Delay.componentServers D k)) ∧
    (∀ k : BipartiteMatchingHT.Delay.Component D, ∀ A : Finset (Fin m),
      A ⊂ BipartiteMatchingHT.Delay.componentServers D k →
      BipartiteMatchingHT.Delay.onlyClasses D.residual A ⊂
        BipartiteMatchingHT.Delay.componentClasses D k ∧
      D.demand (BipartiteMatchingHT.Delay.onlyClasses D.residual A) < D.capacity A ∧
      BipartiteMatchingHT.Delay.onlyClasses D.edge A ⊆
        BipartiteMatchingHT.Delay.onlyClasses D.residual A ∧
      D.demand (BipartiteMatchingHT.Delay.onlyClasses D.edge A) < D.capacity A) ∧
    (∀ σ ∈ BipartiteMatchingHT.Delay.orders D, ∀ r : ℕ,
      1 ≤ r → r ≤ BipartiteMatchingHT.Delay.componentCount D →
      BipartiteMatchingHT.Delay.onlyClasses D.residual
        (BipartiteMatchingHT.Delay.prefixServers D σ r) =
          BipartiteMatchingHT.Delay.prefixClasses D σ r ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
        D.slack ρ (BipartiteMatchingHT.Delay.prefixServers D σ r) =
          (1 - ρ) * D.capacity (BipartiteMatchingHT.Delay.prefixServers D σ r)) := by sorry

end BipartiteMatchingHT.Delay
