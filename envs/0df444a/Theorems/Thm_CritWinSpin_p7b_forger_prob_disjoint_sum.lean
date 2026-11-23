-- Prove2me | Theorems.Thm_CritWinSpin_p7b_forger_prob_disjoint_sum
-- name    : CritWinSpin.p7b_forger_prob_disjoint_sum
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:44:52.757489+00:00
-- url     : https://prove2.me/theorems/dc726d53-dfc3-4dd5-b4e8-7370a475b9da
-- title:
--   Finite additivity for fresh-forgery output events
-- statement:
--   Let $B$ be a PPT algorithm run on input $u$, let $G$ be a property of binary configurations, and suppose that for every configuration $y$ a real number $q_y$ is at most the probability that $B$ outputs exactly $y$ and $G(y)$ holds. Then
--
--   $$
--   \sum_y q_y \le \Pr_B\bigl[\exists y:\ B(u)=y\ \text{and}\ G(y)\bigr].
--   $$
--
--   Indeed, the events “$B$ outputs $y$ and $G(y)$ holds” are pairwise disjoint as $y$ ranges over the finite configuration space. This finite-additivity step is what allows the per-output PPT simulation in the proof of Theorem 7.2 to be recombined into a bound for the whole fresh-forgery event.
--
--   **Formalization Note** No decidability, nonnegativity, or totality assumption on $q$ is required. The conclusion uses the exact output representation `List.ofFn y`, so output events for distinct configurations cannot overlap.
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), §7, p.27, proof of Theorem 7.2 (the probability of producing a fresh valid configuration is the sum over the possible returned configurations).

import Mathlib
import Definitions.Def_CritWinSpin_ForgerScore
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
set_option autoImplicit false

namespace CritWinSpin

open Classical in
/-- A pointwise lower bound for each possible returned configuration gives the corresponding
bound for the fresh-forgery event, since the per-configuration output events are disjoint. -/
theorem p7b_forger_prob_disjoint_sum {n : ℕ} (B : PPT) (u : Str) (G : BinCfg n → Prop)
    (q : BinCfg n → ℝ)
    (hq : ∀ y, q y ≤ B.prob u (fun s => s = List.ofFn y ∧ G y)) :
    (∑ y, q y) ≤ B.prob u (fun s => ∃ y : BinCfg n, s = List.ofFn y ∧ G y) := by sorry
