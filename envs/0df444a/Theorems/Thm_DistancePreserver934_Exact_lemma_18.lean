-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_lemma_18
-- name    : DistancePreserver934.Exact.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:38:50.52295+00:00
-- url     : https://prove2.me/theorems/aab8ea51-797e-4a7f-b954-43c8d4d07f94
-- title:
--   Lemma 18 (volume-decreasing clustering)
-- statement:
--   Let $H$ be a graph with $|V_H|\le n$, let $W\subseteq V_H$ and $a>0$ real, and put $v_x=|B_H(x,a)|$. There are centers $C\subseteq W$ and a partition $W=\bigsqcup_{c\in C}W_c$ into nonempty blocks such that
--   $$W_c\subseteq B_H(c,2a),\qquad v_x\le v_c\ (x\in W_c),\qquad\sum_{c\in C}v_c\le n,\qquad\sum_{c\in C}|W_c|=|W|\le n.$$
--
--   The radius $a$ may be smaller than $1$, $W$ may be empty and $H$ may be disconnected. In the proof of Lemma 10 it is applied with $W=V^*$ and $a=r$.
--
--   **Formalization Note** The partition is given by an assignment $\sigma:W\to C$, with $W_c=\{x\in W:\sigma(x)=c\}$.
--
--   Differences from the source:
--   - generalization: H the minimal distance preserver of the §5 context → H an arbitrary graph on V with |V| ≤ n; reason: the statement and its proof use only the graph metric of H and |V_H| ≤ n
--   - reading: a partition W = ⨆_{c ∈ C} W_c → an assignment σ of W to C whose fibres W_c are all nonempty; reason: a partition indexed by C has nonempty blocks; the assignment encodes disjointness and covering
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026), SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b, Lemma 18, printed p. 18 (PDF p. 19)

import Mathlib
import Definitions.Def_DistancePreserver934_Exact_Preservers
import Definitions.Def_DistancePreserver934_Exact_LoyalCore

namespace DistancePreserver934.Exact

open Classical

/-- Lemma 18 (volume-decreasing clustering), printed p.18 / PDF p.19.  Let `H` be a graph with
`|V_H| ≤ n`, `W ⊆ V_H` and `a > 0`, and put `v_x = |B_H(x, a)|`.  There are centers `C ⊆ W` and a
partition `W = ⨆_{c ∈ C} W_c` (given by the assignment `σ`, with nonempty blocks
`W_c = {x ∈ W : σ x = c}`) such that `W_c ⊆ B_H(c, 2a)`, `v_x ≤ v_c` for `x ∈ W_c`,
`∑_{c ∈ C} v_c ≤ n` and `∑_{c ∈ C} |W_c| = |W| ≤ n`. -/
theorem lemma_18 {V : Type} [Fintype V] (H : SimpleGraph V) (n : ℕ)
    (hV : Fintype.card V ≤ n) (W : Finset V) (a : ℝ) (ha : 0 < a) :
    ∃ (Cs : Finset V) (σ : V → V), Cs ⊆ W ∧ (∀ x ∈ W, σ x ∈ Cs) ∧
      (∀ c ∈ Cs, ∃ x ∈ W, σ x = c) ∧
      (∀ x ∈ W, x ∈ ball H (σ x) (2 * a)) ∧
      (∀ x ∈ W, vol H x a ≤ vol H (σ x) a) ∧
      ∑ c ∈ Cs, vol H c a ≤ n ∧
      ∑ c ∈ Cs, (W.filter (fun x => σ x = c)).card = W.card ∧ W.card ≤ n := by sorry

end DistancePreserver934.Exact
