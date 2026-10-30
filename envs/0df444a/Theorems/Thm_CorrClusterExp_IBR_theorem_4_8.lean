-- Prove2me | Theorems.Thm_CorrClusterExp_IBR_theorem_4_8
-- name    : CorrClusterExp.IBR.theorem_4_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:05.3798+00:00
-- url     : https://prove2.me/theorems/8d59bcb9-4758-4908-b32a-5b0820fba595
-- title:
--   Theorem 4.8, p. 24 — the optimal IBR experiment is asymptotically optimal: (V^DP − V^LB)/V^LB ≤ C(q)·√(w₁²/Σwᵢ²) and V^DP/V^OPT → 1
-- statement:
--   Let $0<q\le\tfrac12$. For sorted cluster sizes $w_1\ge w_2\ge\dots\ge w_n\ge0$ with $w_1>0$, write $V^{\mathrm{DP}}$ for the worst-case variance of the optimal IBR experiment, $V^{\mathrm{OPT}}$ for the optimal value of (1), and $V^{\mathrm{LB}}$ for that of the relaxation (5).
--
--   1. **Rate.** There is a constant $C=C(q)$, depending only on $q$, such that for every $n$ and every such $w$,
--   $$
--   \frac{V^{\mathrm{DP}}-V^{\mathrm{LB}}}{V^{\mathrm{LB}}}\le C\,\sqrt{\frac{w_1^2}{\sum_{i\in[n]}w_i^2}} .
--   $$
--   2. **Asymptotic optimality.** Along every sequence of instances $w^{(m)}$ (on $N_m$ clusters) with no dominating cluster, i.e. $w_1^{(m)2}/\sum_i w_i^{(m)2}\to0$,
--   $$
--   \frac{V^{\mathrm{DP}}-V^{\mathrm{LB}}}{V^{\mathrm{LB}}}\to0\qquad\text{and}\qquad\frac{V^{\mathrm{DP}}}{V^{\mathrm{OPT}}}\to1 .
--   $$
--
--   This is the paper's main asymptotic result: when no cluster dominates, the simple IBR design loses nothing to the optimal (generally intractable) experiment, at rate $O(\sqrt{w_1^2/\sum_iw_i^2})$.
--
--   **Formalization Note** Since $w_1^2/\sum_iw_i^2\ge 1/n$, the hypothesis $w_1^2=o(\sum_iw_i^2)$ already forces the number of clusters to grow, so no separate hypothesis $N_m\to\infty$ is stated. $w_1$ is `w ⟨0, hn⟩` (0-based).
--
--   Differences from the source:
--   - reading: $(V^{\mathrm{DP}}-V^{\mathrm{LB}})/V^{\mathrm{LB}}=O(\sqrt{w_1^2/\sum_iw_i^2})$ → $\exists\,C$ chosen after $q$ and before $n,w$ with the bound for every instance; reason: the paper's $O(\cdot)$ hides the constant $C(q)$ of Lemma 4.7, which depends only on $q$.
--   - generalization: the $O$-bound as $w_1^2/\sum_iw_i^2\to0$ → the bound for every instance with $w_1>0$; reason: the paper's own chain on p. 24 gives it for every ratio in $(0,1]$; the asymptotic statement is an instance.
--   - reading: "asymptotically optimal when $n$ grows large and $w_1^2=o(\sum_iw_i^2)$" → along every sequence with $w_1^2/\sum_iw_i^2\to0$, both the rate quotient $\to0$ and $V^{\mathrm{DP}}/V^{\mathrm{OPT}}\to1$; reason: the definition of asymptotic optimality, and the page's "$\to 0$".
--   - encoding: "$n$ grows large" → no separate hypothesis; reason: $w_1^2/\sum_iw_i^2\ge1/n$, so the ratio tending to $0$ forces $n\to\infty$.
--   - encoding: no hypothesis beyond the standing ones → $0<w_1$; reason: excludes only the all-zero instance, where every ratio is $0/0$.
-- source:
--   Candogan, Chen, Niazadeh, Correlated Cluster-Based Randomized Experiments: Robust Variance Minimization, SSRN 3852100 (version of March 22, 2023), p. 24, Theorem 4.8

import Mathlib
import Definitions.Def_CorrClusterExp_IBR_Setting

namespace CorrClusterExp.IBR

theorem theorem_4_8 (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) :
    (∃ C : ℝ, ∀ (n : ℕ) (hn : 0 < n) (w : Fin n → ℝ), (∀ i, 0 ≤ w i) → Antitone w →
        0 < w ⟨0, hn⟩ →
        (VDP q w - VLB w) / VLB w ≤ C * Real.sqrt (w ⟨0, hn⟩ ^ 2 / ∑ i, w i ^ 2)) ∧
    ∀ (N : ℕ → ℕ) (hN : ∀ m, 0 < N m) (W : ∀ m, Fin (N m) → ℝ),
      (∀ m i, 0 ≤ W m i) → (∀ m, Antitone (W m)) → (∀ m, 0 < W m ⟨0, hN m⟩) →
      Filter.Tendsto (fun m => W m ⟨0, hN m⟩ ^ 2 / ∑ i, W m i ^ 2) Filter.atTop (nhds 0) →
      Filter.Tendsto (fun m => (VDP q (W m) - VLB (W m)) / VLB (W m)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun m => VDP q (W m) / VOPT q (W m)) Filter.atTop (nhds 1) := by sorry

end CorrClusterExp.IBR
