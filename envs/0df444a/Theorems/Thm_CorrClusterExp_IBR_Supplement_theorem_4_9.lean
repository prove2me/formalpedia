-- Prove2me | Theorems.Thm_CorrClusterExp_IBR_Supplement_theorem_4_9
-- name    : CorrClusterExp.IBR.Supplement.theorem_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:27:16.03106+00:00
-- url     : https://prove2.me/theorems/5d0067dd-e374-43d9-93b4-5c9205c9be34
-- title:
--   Theorem 4.9, p. 25 — high-multiplicity model: one IBR block per size has V − V^LB ≤ ¼Σ_k w_k²(min{n_k, w₁²n/(w_k²n_k)} + 2/(q(1−q)) + 4)
-- statement:
--   Let $0<q\le\tfrac12$. In the **high-multiplicity model** the cluster sizes take only $K\ge1$ values $w_1>w_2>\dots>w_K>0$; let $n_k\ge1$ be the number of clusters of size $w_k$ and $n=\sum_{k\in[K]}n_k$. Sort the clusters by decreasing size and consider the simple IBR experiment with one block for each cluster size (block $k$ holds the $n_k$ clusters of size $w_k$, randomized by the law of Proposition 3.1, independently across blocks). Let $V$ be its worst-case variance and $V^{\mathrm{LB}}$ the optimal value of the relaxation (5). Then:
--
--   1. The gap satisfies
--   $$
--   V-V^{\mathrm{LB}}\le\frac14\sum_{k\in[K]}w_k^2\left(\min\Big\{n_k,\frac{w_1^2n}{w_k^2n_k}\Big\}+\frac{2}{q(1-q)}+4\right).
--   $$
--   2. The right-hand side grows at most like $\sqrt n$ while $V^{\mathrm{LB}}$ grows like $n$, with constants depending only on $q$ and the size values:
--   $$
--   \text{RHS}\le\frac14\sum_{k\in[K]}\Big(w_1w_k\sqrt n+w_k^2\Big(\frac{2}{q(1-q)}+4\Big)\Big),\qquad \frac{w_K^2}{4}\,n\le V^{\mathrm{LB}}\le w_1^2\,n .
--   $$
--   3. If moreover $n_k=\alpha_kn$ with $\alpha_k\in(0,1)$ for every $k$, then
--   $$
--   V-V^{\mathrm{LB}}\le\sum_{k\in[K]}\left\{\frac{w_1^2}{4\alpha_k}+w_k^2\Big(\frac{1}{2q(1-q)}+1\Big)\right\},
--   $$
--   a constant independent of $n$.
--
--   The theorem shows that when cluster sizes come from a fixed finite set in fixed proportions, the simplest IBR experiment loses only an additive constant against the lower bound $V^{\mathrm{LB}}\le V^{\mathrm{OPT}}$, a stronger guarantee than the relative rate of Theorem 4.8.
--
--   **Formalization Note** The instance is a composition $c$ of $n$ into $K$ consecutive blocks, values $v_0>v_1>\dots>v_{K-1}>0$ (0-based: $v_0$ is the paper's $w_1$, $v_{K-1}$ its $w_K$), and sizes $w$ with $w_i=v_k$ for every cluster $i$ of block $k$; the strict decrease of $v$ says that the blocks are exactly the classes of equal size, and makes $w$ sorted. $n_k$ is the length of block $k$, $V$ is the published `VIBR q w c` and $V^{\mathrm{LB}}$ the published `VLB w`.
--
--   Differences from the source:
--   - encoding: cluster sizes take K values, with $w_k$ possibly $0$ → the K values are positive and $K\ge1$; reason: the printed ratio $w_1^2n/(w_k^2n_k)$ is undefined at $w_k=0$ and the theorem names $w_1$; positive values are the domain on which the printed formula is defined.
--   - reading: "the right-hand side scales with n at most at a square-root rate (whereas V^LB = Θ(n))" → the explicit bounds RHS $\le\frac14\sum_k(w_1w_k\sqrt n+w_k^2(2/(q(1-q))+4))$ and $\frac{w_K^2}{4}n\le V^{\mathrm{LB}}\le w_1^2n$, valid for every instance; reason: the asymptotic claim is about fixed size values with growing counts, and these bounds (from $\min\{a,b\}\le\sqrt{ab}$ and Lemma 4.2) give it with constants depending only on $q$ and the values.
-- source:
--   Candogan, Chen, Niazadeh, Correlated Cluster-Based Randomized Experiments: Robust Variance Minimization, SSRN 3852100 (version of March 22, 2023), p. 25, Theorem 4.9 (proof: App. B.9, pp. 47–50)

import Mathlib
import Definitions.Def_CorrClusterExp_IBR_Setting

namespace CorrClusterExp.IBR.Supplement

open Finset

theorem theorem_4_9 (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (n : ℕ) (c : Composition n)
    (hK : 0 < c.length) (v : Fin c.length → ℝ) (hv : StrictAnti v) (hvpos : ∀ k, 0 < v k)
    (w : Fin n → ℝ) (hw : ∀ (k : Fin c.length) (i : Fin (c.blocksFun k)), w (c.embedding k i) = v k) :
    VIBR q w c - VLB w ≤
        1 / 4 * ∑ k : Fin c.length, v k ^ 2 *
          (min (c.blocksFun k : ℝ) (v ⟨0, hK⟩ ^ 2 * n / (v k ^ 2 * c.blocksFun k)) +
            2 / (q * (1 - q)) + 4) ∧
      (1 / 4 * ∑ k : Fin c.length, v k ^ 2 *
          (min (c.blocksFun k : ℝ) (v ⟨0, hK⟩ ^ 2 * n / (v k ^ 2 * c.blocksFun k)) +
            2 / (q * (1 - q)) + 4) ≤
        1 / 4 * ∑ k : Fin c.length,
          (v ⟨0, hK⟩ * v k * Real.sqrt n + v k ^ 2 * (2 / (q * (1 - q)) + 4)) ∧
        v ⟨c.length - 1, Nat.sub_lt hK Nat.one_pos⟩ ^ 2 / 4 * n ≤ VLB w ∧
        VLB w ≤ v ⟨0, hK⟩ ^ 2 * n) ∧
      ∀ α : Fin c.length → ℝ, (∀ k, 0 < α k ∧ α k < 1) →
        (∀ k, (c.blocksFun k : ℝ) = α k * n) →
        VIBR q w c - VLB w ≤
          ∑ k : Fin c.length, (v ⟨0, hK⟩ ^ 2 / (4 * α k) +
            v k ^ 2 * (1 / (2 * q * (1 - q)) + 1)) := by sorry

end CorrClusterExp.IBR.Supplement
