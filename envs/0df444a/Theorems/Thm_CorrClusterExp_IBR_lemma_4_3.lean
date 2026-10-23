-- Prove2me | Theorems.Thm_CorrClusterExp_IBR_lemma_4_3
-- name    : CorrClusterExp.IBR.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:07.187802+00:00
-- url     : https://prove2.me/theorems/0a94d1e2-e836-4aeb-9495-f002319ecd51
-- title:
--   Lemma 4.3, p. 19 — the k-partition IBR experiment satisfies V^k/V^LB ≤ f_q(k)(4/k + (k−1)/k·w₁²/V^LB) ≤ f_q(k)(4/k + (k−1)/k)
-- statement:
--   Let $0<q\le\tfrac12$, let $k\ge 1$ be an integer, and let $w_1\ge w_2\ge\dots\ge w_n\ge 0$ be sorted cluster sizes with $n\ge1$ and $w_1>0$. Then the worst-case variance $V^k$ of the $k$-partition IBR experiment satisfies
--   $$
--   \frac{V^k}{V^{\mathrm{OPT}}}\le\frac{V^k}{V^{\mathrm{LB}}}\le f_q(k)\Big(\frac4k+\frac{k-1}{k}\,\frac{w_1^2}{V^{\mathrm{LB}}}\Big)\le f_q(k)\Big(\frac4k+\frac{k-1}{k}\Big),
--   $$
--   where $f_q(k)$ is the optimal value of (1) for the instance with $k$ clusters all of size one.
--
--   The lemma bounds the approximation ratio of a simple IBR experiment by a quantity that depends on $q$ and $k$ only.
--
--   Differences from the source:
--   - encoding: "for any integer $k$" → $k\ge 1$; reason: $k$-partitions and $4/k$ need a positive $k$.
--   - encoding: no hypothesis on the sizes beyond the standing ones → $0<w_1$ (and $n\ge1$); reason: excludes only the all-zero instance, where every ratio is $0/0$.
-- source:
--   Candogan, Chen, Niazadeh, Correlated Cluster-Based Randomized Experiments: Robust Variance Minimization, SSRN 3852100 (version of March 22, 2023), p. 19, Lemma 4.3

import Mathlib
import Definitions.Def_CorrClusterExp_IBR_Setting

namespace CorrClusterExp.IBR

theorem lemma_4_3 (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (k : ℕ) (hk : 1 ≤ k) (n : ℕ)
    (hn : 0 < n) (w : Fin n → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw : Antitone w)
    (hw1 : 0 < w ⟨0, hn⟩) :
    Vk q k w / VOPT q w ≤ Vk q k w / VLB w ∧
      Vk q k w / VLB w ≤
        fq q k * (4 / k + ((k : ℝ) - 1) / k * (w ⟨0, hn⟩ ^ 2 / VLB w)) ∧
      fq q k * (4 / k + ((k : ℝ) - 1) / k * (w ⟨0, hn⟩ ^ 2 / VLB w)) ≤
        fq q k * (4 / k + ((k : ℝ) - 1) / k) := by sorry

end CorrClusterExp.IBR
