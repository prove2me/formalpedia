-- Prove2me | Theorems.Thm_CorrClusterExp_IBR_theorem_4_5
-- name    : CorrClusterExp.IBR.theorem_4_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:16.019288+00:00
-- url     : https://prove2.me/theorems/84f19840-9c7d-4826-9c47-88870e48d455
-- title:
--   Theorem 4.5, p. 21 — V^DP/V^OPT ≤ V^DP/V^LB ≤ min_{k∈ℕ+} V^k/V^LB ≤ min_{k∈ℕ+} f_q(k)(4/k + (k−1)/k)
-- statement:
--   Let $0<q\le\tfrac12$ and let $w_1\ge w_2\ge\dots\ge w_n\ge 0$ be sorted cluster sizes with $n\ge 1$ and $w_1>0$. The worst-case variance $V^{\mathrm{DP}}$ of the optimal IBR experiment (from solving the DP (4)) satisfies
--   $$
--   \frac{V^{\mathrm{DP}}}{V^{\mathrm{OPT}}}\le\frac{V^{\mathrm{DP}}}{V^{\mathrm{LB}}}\le\min_{k\in\mathbb N_+}\frac{V^k}{V^{\mathrm{LB}}}\le\min_{k\in\mathbb N_+}f_q(k)\Big(\frac4k+\frac{k-1}{k}\Big).
--   $$
--   For example, the optimal IBR experiment is a $7/3$-approximation at $q=\tfrac12$.
--
--   **Formalization Note** The minima over $k\in\mathbb N_+$ are written as real infima `⨅ k : ℕ+`. Both families are bounded below by $0$, so the infima are the true infima; both are attained (for $k\ge n$, $V^k=V^{\mathrm{DP}}$; and $f_q(k)(4/k+(k-1)/k)\to\infty$), as the paper's "min" asserts.
--
--   Differences from the source:
--   - encoding: $\min_{k\in\mathbb N_+}$ → `⨅ k : ℕ+` in $\mathbb R$; reason: the families are bounded below by 0 and their minima exist, so the infimum is the minimum.
--   - encoding: no hypothesis on the sizes beyond the standing ones → $0<w_1$ (and $n\ge1$); reason: excludes only the all-zero instance, where every ratio is $0/0$.
-- source:
--   Candogan, Chen, Niazadeh, Correlated Cluster-Based Randomized Experiments: Robust Variance Minimization, SSRN 3852100 (version of March 22, 2023), p. 21, Theorem 4.5

import Mathlib
import Definitions.Def_CorrClusterExp_IBR_Setting

namespace CorrClusterExp.IBR

theorem theorem_4_5 (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (n : ℕ) (hn : 0 < n)
    (w : Fin n → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw : Antitone w) (hw1 : 0 < w ⟨0, hn⟩) :
    VDP q w / VOPT q w ≤ VDP q w / VLB w ∧
      VDP q w / VLB w ≤ ⨅ k : ℕ+, Vk q k w / VLB w ∧
      ⨅ k : ℕ+, Vk q k w / VLB w ≤ ⨅ k : ℕ+, fq q k * (4 / k + ((k : ℝ) - 1) / k) := by sorry

end CorrClusterExp.IBR
