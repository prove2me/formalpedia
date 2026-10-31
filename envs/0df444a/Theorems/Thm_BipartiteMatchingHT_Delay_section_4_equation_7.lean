-- Prove2me | Theorems.Thm_BipartiteMatchingHT_Delay_section_4_equation_7
-- name    : BipartiteMatchingHT.Delay.section_4_equation_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T19:14:35.106988+00:00
-- url     : https://prove2.me/theorems/73b6f258-2fdd-43d2-802c-e8154ce74f28
-- title:
--   Section 4, equation (7) — stationary product form
-- statement:
--   For every heavy-traffic admissible matching and every fixed $0<\rho<1$, the operational queue has a stationary probability law. There exists one normalizing constant $B>0$ such that every compressed state $x=(s_1,n_1,\ldots,s_b,n_b,s_{b+1},\ldots,s_m)$ has probability
--   $$\pi_\rho(x)=B\prod_{\ell=1}^b\frac{\lambda_{U(s_1,\ldots,s_\ell)}^{n_\ell}}{\mu_{\{s_1,\ldots,s_\ell\}}^{n_\ell+1}}\prod_{\ell=b+1}^m\lambda_{C(s_\ell,\ldots,s_m)}^{-1}.$$
--   These probabilities sum to one over all $b=0,\ldots,m$, all server permutations, and every nonnegative integer waiting vector. This is an identity for the genuine queue's observed stationary law. The paper attributes it to Adan and Weiss (2014), Theorem 2.1.
--
--   Differences from the source:
--   - encoding: classes and servers indexed from 1; binary matrix and arbitrary rewards → Fin n and Fin m indexed from 0; Boolean compatibility; omit rewards; reason: reindexing preserves all instances and rewards do not affect queue dynamics or delays
--   - encoding: independent Poisson arrivals and exponential services under FCFS-ALIS → a finite-mark Poisson event chain with null idle-server events and explicit ordered-list updates; reason: constant-rate uniformization gives the same countable-state queue; no finite queue cap or rate restriction is imposed
--   - encoding: the limiting family of operationally stable matchings → existence of a supported invariant probability vector for every real load sufficiently close to 1 from below; reason: stationarity is invariant under constant-rate uniformization; the limiting family is interpreted as eventual membership, without assuming any slack or delay theorem
--   - encoding: the stationary probabilities of compressed states → sums over the fibers of the actual reachable queue-state equilibrium law; reason: retains in-service customer classes for operational dynamics, then forgets them only in the observation map; includes busy count zero
--   - encoding: B is an appropriate normalizing constant → B>0, countable normalization, and operational stationarity are explicit conclusions; reason: makes the stated probability law well-defined rather than defining it by the formula
--   - reading: p. 17 describes n_ell by arrival after the customer at server s_ell and compatibility with the prefix → n_ell counts waiting jobs between consecutive in-service customers, or after the final one; reason: the proof of Lemma 6 on p. 47 explicitly identifies N_ell as the customers between servers s_ell and s_(ell+1); this resolves the abbreviated state description
-- source:
--   Afèche, Caldentey and Gupta, On the Optimal Design of a Bipartite Matching Queueing System, Operations Research (catalog 2021), https://doi.org/10.1287/opre.2020.2027; acquired artifact dated November 3, 2019; citation_basis published; Section 4, equation (7), printed/PDF p. 17

import Definitions.Def_BipartiteMatchingHT_Delay_Aggregates

open scoped BigOperators ENNReal
open Filter Topology

namespace BipartiteMatchingHT.Delay

theorem section_4_equation_7
    {n m : ℕ} (D : BipartiteMatchingHT.Delay.Model n m)
    (hD : BipartiteMatchingHT.Delay.Admissible D)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    BipartiteMatchingHT.Delay.stationary D ρ (BipartiteMatchingHT.Delay.equilibrium D ρ) ∧
    ∃ B : ℝ, 0 < B ∧
      (∀ x : BipartiteMatchingHT.Delay.Compressed m,
        BipartiteMatchingHT.Delay.compressedMass D ρ x =
          ENNReal.ofReal (B * BipartiteMatchingHT.Delay.productFactor D ρ x)) ∧
      (∑' x : BipartiteMatchingHT.Delay.Compressed m,
        ENNReal.ofReal (B * BipartiteMatchingHT.Delay.productFactor D ρ x)) = 1 := by sorry

end BipartiteMatchingHT.Delay
