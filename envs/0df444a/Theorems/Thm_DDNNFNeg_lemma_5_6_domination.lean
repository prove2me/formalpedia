-- Prove2me | Theorems.Thm_DDNNFNeg_lemma_5_6_domination
-- name    : DDNNFNeg.lemma_5_6_domination
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:18:09.500047+00:00
-- url     : https://prove2.me/theorems/c6ef16cd-6490-4fe2-ab81-ea80e3fcc52f
-- title:
--   Proof of Lemma 5.6 — stochastic domination by independent coins
-- statement:
--   Let $(Y_1, \dots, Y_k)$ be random bits and $p \in [0,1]$ such that for every $i$ and every prefix $y_1, \dots, y_{i-1}$ of positive probability
--   $$
--   \mathbb P[Y_i = 1 \mid Y_1 = y_1, \dots, Y_{i-1} = y_{i-1}] \ge p .
--   $$
--   Let $C_1, \dots, C_k$ be independent coins with $\mathbb P[C_i = 1] = p$. Then for every threshold $t$,
--   $$
--   \mathbb P\Big[\sum_{i=1}^k Y_i \ge t\Big] \ge \mathbb P\Big[\sum_{i=1}^k C_i \ge t\Big] = \sum_{j=t}^{k} \binom{k}{j} p^j (1-p)^{k-j}.
--   $$
--
--   In the proof of Lemma 5.6 this is applied with $p = 1/16$ to the free-edge indicators, so that the Chernoff bound for the coins controls the number of free edges.
--
--   **Formalization Note** The law of $(Y_1, \dots, Y_k)$ is a probability weight $w$ on $\{0,1\}^k$, and the conditional hypothesis is written $p \cdot \mathbb P[\text{prefix}] \le \mathbb P[\text{prefix} \wedge Y_i = 1]$.
--
--   Differences from the source:
--   - generalization: the free-edge indicators Yᵢ with p = 1/16 → any law of (Y₁, …, Y_k) on {0,1}^k and any p ∈ [0,1] with the conditional lower bound; reason: the paper's instance satisfies the hypotheses by Eq. (1)
--   - encoding: conditional probabilities of positive-probability prefixes; independent coins C₁, …, C_k → a probability weight w, the multiplicative form p·P[prefix] ≤ P[prefix ∧ Yᵢ = 1], and the binomial sum for P[∑ Cᵢ ≥ t]; reason: same instances; for prefixes of probability 0 the hypothesis is trivial
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), proof of Lemma 5.6, pp.14–15

import Mathlib

namespace DDNNFNeg

/-- **Stochastic domination**, proof of Lemma 5.6 (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), pp.14–15): let `(Y₁, …, Y_k)` be random
bits such that `P[Yᵢ = 1 | Y₁ = y₁, …, Y_{i−1} = y_{i−1}] ≥ p` for every `i` and every prefix of
positive probability. Then for independent coins `C₁, …, C_k` with `P[Cᵢ = 1] = p` and for any
threshold `t`,
`P[∑ Yᵢ ≥ t] ≥ P[∑ Cᵢ ≥ t] = ∑_{j = t}^{k} \binom{k}{j} p^j (1 − p)^{k−j}`.

**Formalization Note** The law of `(Y₁, …, Y_k)` is a probability weight `w` on `{0,1}^k`
(`Fin k → Bool`); the conditional bound is written multiplicatively,
`p · P[prefix] ≤ P[prefix ∧ Yᵢ = 1]`, which is the paper's bound when the prefix has positive
probability and trivial otherwise. The law of `∑ Cᵢ` is written as the binomial sum. The
paper's instance is `p = 1/16` with `Yᵢ` the free-edge indicators; here `p ∈ [0, 1]` and the
law are arbitrary (a generalization). -/
theorem lemma_5_6_domination (k : ℕ) (w : (Fin k → Bool) → ℝ) (hw0 : ∀ ω, 0 ≤ w ω)
    (hw1 : ∑ ω, w ω = 1) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcond : ∀ (i : Fin k) (y : Fin k → Bool),
      p * ∑ ω ∈ Finset.univ.filter (fun ω : Fin k → Bool => ∀ j < i, ω j = y j), w ω ≤
        ∑ ω ∈ Finset.univ.filter (fun ω : Fin k → Bool => (∀ j < i, ω j = y j) ∧ ω i = true), w ω)
    (t : ℕ) :
    ∑ j ∈ Finset.Icc t k, (k.choose j : ℝ) * p ^ j * (1 - p) ^ (k - j) ≤
      ∑ ω ∈ Finset.univ.filter
        (fun ω : Fin k → Bool => t ≤ (Finset.univ.filter (fun i => ω i = true)).card), w ω := by sorry

end DDNNFNeg
