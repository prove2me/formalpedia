-- Prove2me | Theorems.Thm_BipartiteMatchingHT_Delay_theorem_1
-- name    : BipartiteMatchingHT.Delay.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T19:15:06.480374+00:00
-- url     : https://prove2.me/theorems/40f7d245-ad2a-451c-9212-5bae0f16e083
-- title:
--   Theorem 1 — full heavy-traffic class waiting-time formula
-- statement:
--   Fix an arbitrary heavy-traffic admissible FCFS-ALIS bipartite matching with arbitrary positive real rates, fixed positive finite class and server counts, and equal total nominal arrival and service rates. Its finite-load stationary class waiting means exist and are finite for every $0<\rho<1$. Let $(\mathcal C_k,\mathcal S_k)$ be its residual connected components and let $\mathcal T(M)$ contain every destination-first topological order. All order weights are as in Lemma 5, with nonempty order set and positive total weight.
--
--   For every component $k$ and every class $i\in\mathcal C_k$,
--   $$\lim_{\rho\uparrow1}(1-\rho)W_i(\rho)=\sum_{\sigma\in\mathcal T(M)}\frac{Q_\sigma}{\sum_{\tau\in\mathcal T(M)}Q_\tau}\,w_{\sigma,k},$$
--   where
--   $$Q_\sigma=\prod_{r=1}^K\left(\sum_{\ell=1}^r\mu_{\mathcal S_{\sigma(\ell)}}\right)^{-1},\qquad w_{\sigma,k}=\sum_{r=\sigma^{-1}(k)}^K\left(\sum_{\ell=1}^r\mu_{\mathcal S_{\sigma(\ell)}}\right)^{-1}.$$
--   In particular, any two classes in one component have a common finite scaled-mean limit. This is convergence of actual stationary waiting times until service starts, without any finite-load equality between different classes, rational-rate restriction, connectedness assumption on the original graph, or single-component specialization.
--
--   Differences from the source:
--   - encoding: classes and servers indexed from 1; binary matrix and arbitrary rewards → Fin n and Fin m indexed from 0; Boolean compatibility; omit rewards; reason: reindexing preserves all instances and rewards do not affect queue dynamics or delays
--   - encoding: independent Poisson arrivals and exponential services under FCFS-ALIS → a finite-mark Poisson event chain with null idle-server events and explicit ordered-list updates; reason: constant-rate uniformization gives the same countable-state queue; no finite queue cap or rate restriction is imposed
--   - encoding: the limiting family of operationally stable matchings → existence of a supported invariant probability vector for every real load sufficiently close to 1 from below; reason: stationarity is invariant under constant-rate uniformization; the limiting family is interpreted as eventual membership, without assuming any slack or delay theorem
--   - encoding: numbered maximal connected residual components and their permutations → connected-component quotient and bijections from Fin K to that quotient; reason: enumerates the same components and each reversed topological order exactly once, without choosing an artificial labeling
--   - encoding: stationary mean waiting until service starts → an extended nonnegative tagged-arrival hitting-time tail sum, with finite mean concluded before real conversion; reason: the independent exponential event intervals have mean 1/R, giving the same waiting expectation, including an infinite value when needed
--   - encoding: a real limit as rho increases to 1 → Tendsto along nhdsWithin 1 (Ioo 0 1); reason: states existence of convergence from the specified load interval and never chooses an arbitrary value for an absent limit
--   - encoding: the mean of a CRP class W_k → the formula for each customer class in the component, plus an explicit common-limit assertion; reason: avoids choosing a representative and preserves both printed conclusions without asserting finite-load equality
--   - encoding: well-defined stationary means and normalized order weights → finite means at all positive subunit loads, stable queues, nonempty order set, and positive total weight are explicit conclusions; reason: makes the domain of the source expectation and normalized ratio explicit rather than assuming any derived law
--   - encoding: flows summed only on compatible edges and limiting maximum flows → flows are zero off compatible edges; residual support uses all saturated nominal feasible flows; reason: zero extension preserves the objective, and saturation is the equivalent feasibility test in Remark 3 and equation (6)
-- source:
--   Afèche, Caldentey and Gupta, On the Optimal Design of a Bipartite Matching Queueing System, Operations Research (catalog 2021), https://doi.org/10.1287/opre.2020.2027; acquired artifact dated November 3, 2019; citation_basis published; Theorem 1, printed/PDF p. 20

import Definitions.Def_BipartiteMatchingHT_Delay_Aggregates

open scoped BigOperators ENNReal
open Filter Topology

namespace BipartiteMatchingHT.Delay

theorem theorem_1
    {n m : ℕ} (D : BipartiteMatchingHT.Delay.Model n m)
    (hD : BipartiteMatchingHT.Delay.Admissible D) :
    (∀ ρ : ℝ, 0 < ρ → ρ < 1 → BipartiteMatchingHT.Delay.Stable D ρ ∧
      ∀ i, BipartiteMatchingHT.Delay.meanWait D ρ i < ⊤) ∧
    (BipartiteMatchingHT.Delay.orders D).Nonempty ∧
    0 < BipartiteMatchingHT.Delay.totalQ D ∧
    (∀ k : BipartiteMatchingHT.Delay.Component D,
      ∀ i ∈ BipartiteMatchingHT.Delay.componentClasses D k,
      Tendsto (fun ρ : ℝ => (1 - ρ) * (BipartiteMatchingHT.Delay.meanWait D ρ i).toReal)
        (nhdsWithin 1 (Set.Ioo 0 1)) (nhds (BipartiteMatchingHT.Delay.limitingWait D k))) ∧
    (∀ k : BipartiteMatchingHT.Delay.Component D,
      ∀ i₁ ∈ BipartiteMatchingHT.Delay.componentClasses D k,
      ∀ i₂ ∈ BipartiteMatchingHT.Delay.componentClasses D k,
      ∃ L : ℝ,
        Tendsto (fun ρ : ℝ => (1 - ρ) * (BipartiteMatchingHT.Delay.meanWait D ρ i₁).toReal)
          (nhdsWithin 1 (Set.Ioo 0 1)) (nhds L) ∧
        Tendsto (fun ρ : ℝ => (1 - ρ) * (BipartiteMatchingHT.Delay.meanWait D ρ i₂).toReal)
          (nhdsWithin 1 (Set.Ioo 0 1)) (nhds L)) := by sorry

end BipartiteMatchingHT.Delay
