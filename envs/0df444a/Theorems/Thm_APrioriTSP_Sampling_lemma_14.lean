-- Prove2me | Theorems.Thm_APrioriTSP_Sampling_lemma_14
-- name    : APrioriTSP.Sampling.lemma_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:53.031348+00:00
-- url     : https://prove2.me/theorems/8767599f-e4ff-4b00-9d2f-439976d92e9b
-- title:
--   Lemma 14, p. 12 — the error term beyond bucket N is at most δ1·Σ_{k=0}^N e^{−(k−1)σβ}·B_k + δ2·B_1
-- statement:
--   Let $\alpha \ge 0$, $\sigma > 0$, $\beta > 0$ and $N \in \mathbb N$, and let $(B_i)_{i\ge0}$ be nonnegative with $B_{i+j} \le B_i + B_j$ for all $i, j \ge 1$. With
--   $$\delta_1 = \frac{4\beta}{e^{N\sigma\beta}(e^{\sigma\beta}-1)},\qquad \delta_2 = \Big(\alpha + \frac{2\beta}{e^{N\sigma\beta}(e^{\sigma\beta}-1)}\Big)\cdot\frac{e^{-N\sigma\beta}}{(1-e^{-\sigma\beta})^2}\cdot(1 + N - e^{-\sigma\beta}N),$$
--   we have
--   $$\alpha\sum_{k=N+1}^\infty e^{-(k-1)\sigma\beta}B_k + 2\beta\sum_{\substack{i,j\in\mathbb Z_{\ge0}\\ \max\{i,j\}>N}} e^{-(i+j-1)\sigma\beta}\min\{B_i,B_j\} \;\le\; \delta_1\sum_{k=0}^N e^{-(k-1)\sigma\beta}B_k + \delta_2 B_1 .$$
--
--   The lemma bounds the contribution of buckets beyond $N$ to the bucket form (10) of the sampling constraint by terms in $B_0, \dots, B_N$ only, which is what makes (Sampling-LP) finite.
--
--   **Formalization Note** The first series is a `tsum` over $k \in \mathbb N$ of terms that vanish for $k \le N$; the double series is a `tsum` over $\mathbb N \times \mathbb N$ of terms that vanish when $\max\{i,j\} \le N$. Under the hypotheses $B_k \le kB_1$ for $k \ge 1$, so both families are summable. Exponents are real: $k = 0$ gives $e^{\sigma\beta}$.
--
--   Differences from the source:
--
--   - reading: δ1 · Σ_{k=0}^N e^{−(k−1)·σβ} · B_i (the summand's index i is unbound) → δ1 · Σ_{k=0}^N e^{−(k−1)σβ} · B_k; reason: the only well-formed reading; it is the sum (11) and (13) use, and the proof's last line (p. 14) has the same sum with index and summand i
--   - generalization: the buckets B of a feasible solution of (Sampling-OP) (B ≥ 0 and Proposition 12) → any sequence B ≥ 0 with B_{i+j} ≤ B_i + B_j for i, j ≥ 1; reason: the proof uses only these two properties, which the buckets of a feasible solution have
--   - generalization: α ≥ 1, the approximation guarantee of the TSP algorithm of step (ii) (p. 4) → every real α ≥ 0; reason: (2) is a formula in α and the argument uses only α ≥ 0; at every α ≥ 1 the Lean statement is the paper's
--   - generalization: σ = 0.663, fixed at the start of §2 (p. 7) → every σ > 0; reason: the proof uses only σβ > 0; σ = 0.663 is an instance
--   - encoding: N an integer (the buckets B_0, …, B_N) → N ∈ ℕ; reason: N indexes the buckets kept, so N ≥ 0
--   - encoding: the series over k ≥ N + 1 and over i, j ∈ ℤ_{≥0} with max{i, j} > N → `tsum`s over ℕ and ℕ × ℕ of the terms multiplied by the indicator of the index range; reason: same sums; the families are nonnegative and summable since B_k ≤ k·B_1
-- source:
--   Blauth, Neuwohner, Puhlmann & Vygen, Improved guarantees for the a priori TSP, arXiv:2309.10663v1, p. 12, Lemma 14 (proof p. 14)

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting
import Definitions.Def_APrioriTSP_Sampling_LP

namespace APrioriTSP.Sampling

/-- Lemma 14 (p. 12): the error term beyond bucket `N` is bounded by
`δ₁ Σ_{k=0}^N e^{−(k−1)σβ} B_k + δ₂ B_1`. -/
theorem lemma_14 (α σ β : ℝ) (hα : 0 ≤ α) (hσ : 0 < σ) (hβ : 0 < β) (N : ℕ)
    (B : ℕ → ℝ) (hB0 : ∀ i, 0 ≤ B i)
    (hB : ∀ i j, 1 ≤ i → 1 ≤ j → B (i + j) ≤ B i + B j) :
    α * ∑' k : ℕ, (if N < k then Real.exp (-(((k : ℝ) - 1) * σ * β)) * B k else 0) +
        2 * β * ∑' q : ℕ × ℕ, (if N < max q.1 q.2 then
          Real.exp (-(((q.1 : ℝ) + q.2 - 1) * σ * β)) * min (B q.1) (B q.2) else 0) ≤
      delta1 β σ N * ∑ k ∈ Finset.range (N + 1), Real.exp (-(((k : ℝ) - 1) * σ * β)) * B k +
        delta2 α β σ N * B 1 := by sorry

end APrioriTSP.Sampling
