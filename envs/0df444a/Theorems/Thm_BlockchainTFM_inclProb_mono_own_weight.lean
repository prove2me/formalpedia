-- Prove2me | Theorems.Thm_BlockchainTFM_inclProb_mono_own_weight
-- name    : BlockchainTFM.inclProb_mono_own_weight
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:02:42.404906+00:00
-- url     : https://prove2.me/theorems/50200d37-48bc-44ed-9788-10cd25ef1121
-- title:
--   EC.4.4.1: the allocation of Mechanism 3 is monotone in the own bid (stated for any positive weights)
-- statement:
--   Consider $k$ rounds of weighted sampling without replacement among $n$ users with positive weights $w_1,\dots,w_n$, and let $a_i(w)$ be the probability that user $i$ is drawn. Raising user $i$'s own weight does not lower this probability: for all $0<x\le y$, with the other weights fixed,
--   $$a_i(w_i=x,\ \mathbf w_{-i})\ \le\ a_i(w_i=y,\ \mathbf w_{-i}).$$
--
--   In Mechanism 3 the weights are $w_j=e^{mb_j}$ with $m\ge0$, so for every $\mathbf b_{-i}$, $a_i(b_i,\mathbf b_{-i})\ge a_i(b_i',\mathbf b_{-i})$ whenever $b_i\ge b_i'$, which is the monotonicity that Myerson's Lemma and Theorem 2 require. The case $n\le k$, where every $a_i=1$, is included.
--
--   **Formalization Note** The inclusion probability is the sum over $t=1,\dots,k$ of the probabilities (24) of all injective outcome sequences of length $t$ ending with $i$.
--
--   Differences from the source:
--   - generalization: a_i(b_i, b_{−i}) ≥ a_i(b'_i, b_{−i}) for b_i ≥ b'_i, with weights e^{m b_j} → inclusion probability non-decreasing in the own weight, for arbitrary positive weights; reason: for m ≥ 0, b ↦ e^{mb} is non-decreasing and positive, so the paper's statement is the instance w = e^{m b}
--   - encoding: sampling outcomes (j₁,…,j_t) and a_i = Σ_t δ_t(i) → injective maps Fin t ↪ Fin n; inclProb; reason: Lean convention; same quantity
-- source:
--   Chen, Simchi-Levi, Zhao, Zhou, Bayesian Mechanism Design for Blockchain Transaction Fee Allocation, arXiv:2209.13099v7, Appendix EC.4.4.1, p.ec17 (with §6.1 (23)–(25), pp.28–29)

import Mathlib
import Definitions.Def_BlockchainTFM_Sampling

namespace BlockchainTFM

/-- **Monotonicity of the allocation rule**, Chen–Simchi-Levi–Zhao–Zhou, arXiv:2209.13099v7,
Appendix EC.4.4.1, p.ec17: "for any `b_{-i}`, `a_i(b_i, b_{-i}) ≥ a_i(b'_i, b_{-i})` if
`b_i ≥ b'_i`."

Stated for the inclusion probability of `k`-round weighted sampling without replacement with
arbitrary positive weights: raising user `i`'s own weight from `x` to `y ≥ x` (all other weights
fixed) does not decrease the probability that `i` is drawn.

**Formalization Note.** Mechanism 3 uses the weights `w_j = e^{m b_j}`; for `m ≥ 0`,
`b_i ≥ b'_i` gives `e^{m b_i} ≥ e^{m b'_i}`, so this statement contains the paper's for every
`k`, `n`, `m ≥ 0` and `b`. -/
theorem inclProb_mono_own_weight {n : ℕ} (k : ℕ) (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (i : Fin n) (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    inclProb k (Function.update w i x) i ≤ inclProb k (Function.update w i y) i := by sorry

end BlockchainTFM
