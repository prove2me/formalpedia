-- Prove2me | Theorems.Thm_CycleLengthsExp_BetaGraph_condition_1_claim_2
-- name    : CycleLengthsExp.BetaGraph.condition_1_claim_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:24:45.247979+00:00
-- url     : https://prove2.me/theorems/93bc7474-e4a4-4767-86ae-50b253674e87
-- title:
--   p. 18 — condition 1 of Theorem 4.1 with d = 3: |N_H(U)| ≥ 3|U| + 1 for 0 < |U| ≤ βn
-- statement:
--   Let $0<\beta<1/20$, let $G$ be a β-graph on $n$ vertices and $H=G[S]$ an induced subgraph with the size and small-set expansion properties of Lemma 4.1. Then for every $U\subseteq S$ with $0<|U|\le\beta n$,
--   $$|N_H(U)|\ \ge\ \frac{1-3\beta}{2\beta}|U| = 3|U|+\frac{1-9\beta}{2\beta}|U|\ \ge\ 3\,|U|+1 .$$
--
--   This is condition 1 of Theorem 4.1 with $d=3$, used to embed the binary trees $T_{2,r,p}$ that produce the long cycles in Theorem 3.
--
--   **Formalization Note** $N_H(U)$ is written $N_G(U)\cap S$; the inequality is between natural numbers.
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 18, verification of claim (2), condition 1 (d = 3 fixed on p. 17)

import Mathlib
import Definitions.Def_CycleLengthsExp_BetaGraph_Setting

namespace CycleLengthsExp.BetaGraph

/-- Condition 1 of Theorem 4.1 for claim (2) (p. 18): for `0 < β < 1/20`, if `S` satisfies the
conclusion of Lemma 4.1, then every `U ⊆ S` with `0 < |U| ≤ βn` has `|N_H(U)| ≥ 3|U| + 1`. -/
theorem condition_1_claim_2 (β : ℝ) (hβ : 0 < β) (hβ' : β < 1 / 20) (n : ℕ)
    (G : SimpleGraph (Fin n)) (hG : IsBetaGraph β G)
    (S : Set (Fin n)) (hSsize : (1 - β) * n ≤ S.ncard)
    (hS : ∀ U ⊆ S, (U.ncard : ℝ) ≤ β * n →
      (1 - 3 * β) / (2 * β) * U.ncard ≤ (CycleLengthsExp.WellSpread.extNbhd G U ∩ S).ncard)
    (U : Set (Fin n)) (hUS : U ⊆ S) (hU0 : 0 < U.ncard) (hU : (U.ncard : ℝ) ≤ β * n) :
    3 * U.ncard + 1 ≤ (CycleLengthsExp.WellSpread.extNbhd G U ∩ S).ncard := by sorry

end CycleLengthsExp.BetaGraph
