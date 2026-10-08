-- Prove2me | Theorems.Thm_ConstrainedQueueing_Nonstationary_lemma_4_1
-- name    : ConstrainedQueueing.Nonstationary.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:03.950542+00:00
-- url     : https://prove2.me/theorems/0136e92c-7c11-4339-9d06-55c2193e9cd5
-- title:
--   Lemma 4.1, p. 1942 — outside C̄′, max over f ∈ co(S) of the mincut capacity of N_af is attained and is < Σ a_l
-- statement:
--   Let the constraint set $S$ satisfy C.1 and contain the empty activation set, and let $a\in\mathbb R^L$ be a nonnegative rate vector with $a\notin\bar C'$. For $f\in\mathrm{co}(S)$ write $C_{af}((W,W')_{af})$ for the capacity of a minimum cut of the flow network $N_{af}$ (edges $(o,l)$ of capacity $a_l$, one edge of capacity $f_k$ per server $k$). Then the maximum of the mincut capacity over $\mathrm{co}(S)$ is attained at some $f_o\in\mathrm{co}(S)$, and it is strictly below the total arrival rate:
--   $$\sum_{l=1}^L a_l-\max_{f\in\mathrm{co}(S)}C_{af}((W,W')_{af})=\sum_{l=1}^L a_l-C_{af_o}((W,W')_{af_o})>0 .$$
--
--   The cut consisting of all edges $(o,l)$ has capacity $\sum_l a_l$, so the mincut capacity never exceeds the total arrival rate; the lemma says that outside $\bar C'$ this bound is strict, uniformly over the convex hull of the activation vectors. This gap is the $\epsilon$ of Corollary 4.1.
--
--   **Formalization Note.** The conclusion is stated as: there is $f_o\in\mathrm{co}(S)$ with $C_{af}\le C_{af_o}$ for every $f\in\mathrm{co}(S)$ (the maximum is attained at $f_o$) and $C_{af_o}<\sum_l a_l$. The page prints the right-hand sum as $\sum_{i=l}^{L}a_l$ (summation index $i$, summand $a_l$), read as $\sum_{l=1}^{L}a_l$. The page's hypothesis is $a\in(\bar C)^c$, the complement of the closure of the stability region; the formalization uses $\bar C'$, as the introduction of §IV does, and the two coincide by Theorem 3.2 of the paper. The hypotheses $\emptyset\in S$ and $a\ge0$ are the paper's standing conventions (the idle set is an activation set; rates are nonnegative).
-- source:
--   Tassiulas and Ephremides, Stability properties of constrained queueing systems and scheduling policies for maximum throughput in multihop radio networks, IEEE Trans. Automat. Control 37(12) (1992), p. 1942, §IV, Lemma 4.1

import Mathlib
import Definitions.Def_ConstrainedQueueing_Nonstationary_Model

namespace ConstrainedQueueing.Nonstationary

/-- Lemma 4.1 (p. 1942): if the nonnegative rate vector `a` lies outside the closure of `C'`,
then the maximum of the mincut capacity of `N_af` over `f ∈ co(S)` is attained at some
`f_o ∈ co(S)`, and it is strictly smaller than `∑_l a_l`. -/
theorem lemma_4_1 {L N : ℕ} (net : Network L N) (hC1 : C1 net) (hS0 : (∅ : Finset (Fin N)) ∈ net.S)
    (a : Fin L → ℝ) (ha0 : 0 ≤ a) (ha : a ∉ closure (Cprime net)) :
    ∃ fo ∈ coS net, (∀ f ∈ coS net, minCutCap net a f ≤ minCutCap net a fo) ∧
      minCutCap net a fo < ∑ l, a l := by sorry

end ConstrainedQueueing.Nonstationary
