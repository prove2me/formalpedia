-- Prove2me | Theorems.Thm_CorrClusterExp_IBR_eq_13
-- name    : CorrClusterExp.IBR.eq_13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:11.212579+00:00
-- url     : https://prove2.me/theorems/9b3f05b2-67b1-47b8-b2ef-bfee333baa45
-- title:
--   (13), proof of Lemma 4.3, p. 42 — V^k ≤ f_q(k)·S_k with S_k the sum of the squared largest sizes of the groups
-- statement:
--   Let $0<q\le\tfrac12$, $k\ge 1$, and let $w_1\ge\dots\ge w_n\ge 0$ be sorted cluster sizes. Group the clusters into $N=\lceil n/k\rceil$ groups of $k$ consecutive clusters (the last possibly smaller), and let
--   $$
--   S_k=\sum_{i=1}^{N}w_{(i-1)k+1}^2
--   $$
--   be the sum of the squares of the largest cluster size of each group. Then the worst-case variance of the $k$-partition IBR experiment satisfies
--   $$
--   V^k\le f_q(k)\,S_k, \tag{13}
--   $$
--   where $f_q(k)$ is the optimal value of (1) for $k$ clusters of size one.
--
--   This is the first step of the proof of Lemma 4.3.
--
--   **Formalization Note** In 0-based indices the first cluster of group $i$ is index $(i-1)k$, so $S_k$ is the sum of $w_j^2$ over the indices $j<n$ divisible by $k$.
--
--   Differences from the source:
--   - encoding: $S_k=\sum_{i=1}^{N}w^2_{(i-1)k+1}$ with $N=\lceil n/k\rceil$ → $\sum_{j<n,\ k\mid j}w_j^2$ (0-based); reason: the same index set.
--   - encoding: "for any integer $k$" → $k\ge 1$; reason: $k$-partitions need a positive group size.
-- source:
--   Candogan, Chen, Niazadeh, Correlated Cluster-Based Randomized Experiments: Robust Variance Minimization, SSRN 3852100 (version of March 22, 2023), p. 42, Appendix B.6 (proof of Lemma 4.3), equation (13)

import Mathlib
import Definitions.Def_CorrClusterExp_IBR_Setting

namespace CorrClusterExp.IBR

open Finset

theorem eq_13 (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (k : ℕ) (hk : 1 ≤ k) (n : ℕ)
    (w : Fin n → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw : Antitone w) :
    Vk q k w ≤ fq q k * ∑ i ∈ univ.filter (fun i : Fin n => k ∣ i.val), w i ^ 2 := by sorry

end CorrClusterExp.IBR
