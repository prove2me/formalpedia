-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_Supplement_theorem_5_7
-- name    : ArapostathisAC.VanishingDiscount.Supplement.theorem_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:09:12.349812+00:00
-- url     : https://prove2.me/theorems/57b8ef36-f290-4f75-8ef0-8bdc6234e79c
-- title:
--   Theorem 5.7 — with bounded costs, each of the five combinations (5.7, 5.8), (5.9, 5.10), (5.9, 5.11), (5.10, 5.12), (5.11, 5.12) gives an average optimal $f\in\Pi_{SD}$
-- statement:
--   In the countable-state model of §5 with bounded costs (§5.1), consider the conditions: (5.7) for every $f\in\Pi_{SD}$ and $i$ the Cesàro limit $\eta_i(f)(j)=\lim_N N^{-1}\sum_{n<N}P^n(f)(i,j)$ exists and is a probability vector; (5.8) $f\mapsto\eta_i(f)$ is continuous; (5.9) these limits exist and $\{\eta_i(f):f\in\Pi_{SD}\}$ is tight for every $i$; (5.10) every $f\in\Pi_{SD}$ induces a recurrent chain; (5.11) no $f\in\Pi_{SD}$ has two disjoint invariant sets; (5.12) $\{P(f)(i,\cdot):i\in S,f\in\Pi_{SD}\}$ is tight. If one of
--   $$(5.7,5.8),\quad(5.9,5.10),\quad(5.9,5.11),\quad(5.10,5.12),\quad(5.11,5.12)$$
--   holds, then there is $f\in\Pi_{SD}$ with $J(i,f)=J^*(i)$ for every $i$, the infimum $J^*$ being over all admissible policies.
--
--   **Formalization Note** $\Pi_{SD}$ carries the product topology and $\mathcal P(S)$ the weak topology; continuity is stated for sequences ($f_n(k)\to f(k)$ for every $k$ implies $\eta_i(f_n)(j)\to\eta_i(f)(j)$ for every $j$). Tightness on $S=\mathbb N$ means a uniform lower bound $1-\varepsilon$ on the mass of $\{0,\dots,N-1\}$.
--
--   Differences from the source:
--   - reading: §5.1: the cost c is bounded → c(i, a) ≤ C on admissible pairs for some C (c ≥ 0 by Assumption 2.1); reason: the section's standing assumption, which applies to Theorems 5.3–5.7
--   - encoding: continuity of f ↦ η_i(f) (product topology on Π_SD, weak topology on 𝒫(S)) → sequential continuity with pointwise convergence of probability vectors; reason: a countable product of metric spaces is metrizable, and weak convergence of probability vectors on a discrete countable space is pointwise convergence
--   - reading: Assumption 5.9 refers to the measures of Assumption 5.7 → Assumption 5.9 includes the existence part of Assumption 5.7; reason: p. 305: 'By definition, Assumption 5.9 implies Assumption 5.7'
--   - reading: the corresponding process is recurrent → every state is recurrent under f; reason: the usual meaning of a recurrent chain
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 305, Theorem 5.7 and Assumptions 5.7–5.12; p. 301, §5.1 bounded costs

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_StationaryChain
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_Recurrence

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open ArapostathisAC.VanishingDiscount

namespace ArapostathisAC.VanishingDiscount.Supplement

/-- Theorem 5.7 (p. 305), in the bounded-cost setting of §5.1. Each of the five combinations
(5.7, 5.8), (5.9, 5.10), (5.9, 5.11), (5.10, 5.12), (5.11, 5.12) of assumptions is sufficient for
the existence of an average optimal `f ∈ Π_SD`. -/
theorem theorem_5_7 {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (hc : ∃ C : ℝ, ∀ i, ∀ a ∈ M.U i, M.c i a ≤ C)
    (hA : (Assumption57 M ∧ Assumption58 M) ∨ (Assumption59 M ∧ Assumption510 M) ∨
      (Assumption59 M ∧ Assumption511 M) ∨ (Assumption510 M ∧ Assumption512 M) ∨
      (Assumption511 M ∧ Assumption512 M)) :
    ∃ f : StationaryPolicy M, IsAvgOptimal M f := by sorry

end ArapostathisAC.VanishingDiscount.Supplement
