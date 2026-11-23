-- Prove2me | Theorems.Thm_CorrClusterExp_IBR_Supplement_theorem_4_10
-- name    : CorrClusterExp.IBR.Supplement.theorem_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:29:42.103402+00:00
-- url     : https://prove2.me/theorems/64e5e407-9061-4620-b2eb-5b902c0c889f
-- title:
--   Theorem 4.10, p. 26 — the logarithmic-partition IBR experiment is asymptotically optimal: (V − V^LB)/V^LB = O(n^{−c/4} ln n)
-- statement:
--   Let $0<q\le\tfrac12$, $c>0$ and $A>0$. Write $V$ for the worst-case variance of the IBR experiment of the logarithmic partition of §4.2.2 with parameters $\delta_1=\delta_2=c/4$, $V^{\mathrm{LB}}$ for the optimal value of (5) and $V^{\mathrm{OPT}}$ for the optimal value of (1). Assume the strengthened no-dominating-cluster condition
--   $$
--   \frac{\sum_{i=1}^nw_i^2}{w_1^2}\ge A\,n^c .
--   $$
--   1. **Rate.** There are constants $C$ and $N_0$, depending only on $q$, $c$ and $A$, such that for every $n\ge N_0$ and all sorted sizes $w_1\ge\dots\ge w_n\ge0$ with $w_1>0$ satisfying the condition,
--   $$
--   \frac{V-V^{\mathrm{LB}}}{V^{\mathrm{LB}}}\le C\,n^{-c/4}\ln n .
--   $$
--   2. **Asymptotic optimality.** Along every sequence of such instances whose number of clusters tends to infinity and which satisfy the condition eventually, $(V-V^{\mathrm{LB}})/V^{\mathrm{LB}}\to0$ and $V/V^{\mathrm{OPT}}\to1$.
--
--   The theorem shows that a partition computed without any optimization (thresholding plus geometric grouping by the ratio $\alpha$) already gives an asymptotically optimal experiment, at a slower rate and under a slightly stronger condition than the optimal IBR experiment of Theorem 4.8.
--
--   **Formalization Note** Clusters are `Fin n`, 0-based ($w_1$ is `w ⟨0, _⟩`), sorted means `Antitone w`. The partition is `logPartition w (c/4) (c/4)` of the supplement's definition file, $V$ is the published `VIBR`, $V^{\mathrm{LB}}$ and $V^{\mathrm{OPT}}$ the published `VLB` and `VOPT`. The $\Omega(n^c)$ hypothesis is read with an explicit constant $A$, and $O(\cdot)$ with constants $C,N_0$ chosen after $q,c,A$ and before $n$ and $w$. For $c\ge4$ the parameter $c/4$ lies outside the interval $(0,1)$ of §4.2.2; the partition is defined for every positive parameter, and since $\sum_iw_i^2/w_1^2\le n$ the condition with $c>1$ fails for large $n$, so these cases hold trivially, as in the source.
--
--   Differences from the source:
--   - encoding: $w_1>0$ is implicit in the ratio $\sum_iw_i^2/w_1^2$ → $0<w_1$ is a hypothesis; reason: the ratio is undefined at $w_1=0$, so this excludes only undefined cases.
--   - reading: "$\sum_iw_i^2/w_1^2=\Omega(n^c)$" and "$=O(n^{-c/4}\ln n)$" → for each Ω-constant $A>0$ there are $C,N_0$ such that every instance with $n\ge N_0$ and $\sum_iw_i^2/w_1^2\ge An^c$ satisfies the rate bound; reason: the standard uniform reading of the Landau symbols, with constants independent of the instance.
--   - reading: "asymptotically optimal" → along every sequence of instances with $n\to\infty$ satisfying the condition eventually, $V/V^{\mathrm{OPT}}\to1$ (and the rate quotient $\to0$); reason: the paper's notion of asymptotic optimality as $n$ grows; the Ω hypothesis alone does not force $n\to\infty$, so $n\to\infty$ is stated.
-- source:
--   Candogan, Chen, Niazadeh, Correlated Cluster-Based Randomized Experiments: Robust Variance Minimization, SSRN 3852100 (version of March 22, 2023), p. 26, Theorem 4.10 (logarithmic partition: §4.2.2, p. 26; proof: App. B.10, pp. 50–52)

import Mathlib
import Definitions.Def_CorrClusterExp_IBR_Setting
import Definitions.Def_CorrClusterExp_IBR_Supplement_LogPartition

namespace CorrClusterExp.IBR.Supplement

open Finset

theorem theorem_4_10 (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (c : ℝ) (hc : 0 < c) (A : ℝ)
    (hA : 0 < A) :
    (∃ C N₀ : ℝ, ∀ (n : ℕ) (hn : 0 < n) (w : Fin n → ℝ), N₀ ≤ n → (∀ i, 0 ≤ w i) → Antitone w →
        0 < w ⟨0, hn⟩ → A * (n : ℝ) ^ c ≤ (∑ i, w i ^ 2) / w ⟨0, hn⟩ ^ 2 →
        (VIBR q w (logPartition w (c / 4) (c / 4)) - VLB w) / VLB w ≤
          C * (n : ℝ) ^ (-(c / 4)) * Real.log n) ∧
    ∀ (N : ℕ → ℕ) (hN : ∀ m, 0 < N m) (W : ∀ m, Fin (N m) → ℝ),
      Filter.Tendsto N Filter.atTop Filter.atTop →
      (∀ m i, 0 ≤ W m i) → (∀ m, Antitone (W m)) → (∀ m, 0 < W m ⟨0, hN m⟩) →
      (∀ᶠ m in Filter.atTop, A * (N m : ℝ) ^ c ≤ (∑ i, W m i ^ 2) / W m ⟨0, hN m⟩ ^ 2) →
      Filter.Tendsto (fun m => (VIBR q (W m) (logPartition (W m) (c / 4) (c / 4)) - VLB (W m)) /
          VLB (W m)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun m => VIBR q (W m) (logPartition (W m) (c / 4) (c / 4)) / VOPT q (W m))
          Filter.atTop (nhds 1) := by sorry

end CorrClusterExp.IBR.Supplement
