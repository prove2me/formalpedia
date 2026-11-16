-- Prove2me | Theorems.Thm_CompressedOracleDuality_LabelSymmetric_Supplement_lemma_5_8
-- name    : CompressedOracleDuality.LabelSymmetric.Supplement.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T22:09:51.117792+00:00
-- url     : https://prove2.me/theorems/9717ae74-93f1-4055-8a8c-c342d024ae35
-- title:
--   Lemma 5.8 — classical progress against the injective run
-- statement:
--   Let $N=2^n\ge64$, $S\ge n$, and let $B$ be any deterministic label-symmetric branching program of length $T<N/2$, with at most $2^S$ vertices in each internal layer and unrestricted finite output leaves. Fix the canonical injective oracle $H^*(x)=e(x)$ and define $L_t^*=L(\mu_t(H^*))$ from that fixed execution. Let $p$ be the uniform probability, over all functions $H:X\to Y$, that the actual output reports $x_1<x_2$ and $H(x_1)=H(x_2)=y$. Then
--   $$p\le\frac{1+\sum_{t=0}^{T-1}|L_t^*|}{N}.$$
--   There is no success-threshold hypothesis and no square-root restriction on $T$ or on the summation indices. The additive $1/N$ is retained. At $T=0$ the sum is empty and the bound applies to the fixed output. The fixed injective execution determines every summand independently of $H$, so the bound controls actual average collision success.
--
--   Differences from the source:
--   - encoding: one carrier [N] for inputs and labels → published Fin (2^n) inputs and n-bit labels, identified by the fixed most-significant-bit-first bijection e; reason: e transports every oracle and label permutation bijectively; input ordering is the published strict order
--   - encoding: a singleton start layer, exactly 2^S internal vertices, and arbitrarily many terminal leaves → finite layer types with a Unique initial layer and at most 2^S vertices only for 1 <= t < T; reason: padding unreachable internal vertices recovers the printed width without altering executions, symmetry, or success; T=0 retains one fixed output
--   - encoding: the unique minimum matched set for t < N/2 → a minimum-cardinality selector for 2*t < 2^n, with empty-set totalization otherwise; reason: finiteness ensures a minimizer and label symmetry ensures uniqueness in the used regime; no matched-set property is assumed
--   - encoding: H*(x)=x and L*_t on the common input/label carrier → H*(x)=e(x) and label subsets L*_t from the fixed canonical binary identification; reason: e is a bijection between the published bases, so it represents the same fixed injective-oracle comparison
--   - encoding: T < N/2 and the sum over t<T → 2*T < 2^n and a real finite sum indexed by Fin T; reason: the time range and every summand are unchanged; no terminal-layer width restriction is added
-- source:
--   Ding and Zhandry, Compressed Oracle Duality: A simple framework for knowing what quantum adversaries know, October 30, 2026 preprint, arXiv:submit/8306656 [quant-ph], STOC 2027 submission #94; source.pdf SHA-256 6614c6a707d45eff1e475fa25c9c0d22747adf304a0680ebf79d2bd118122daa; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/94.pdf, Lemma 5.8, (84), p.29; proof pp.29-30; standing assumptions p.11

import Definitions.Def_CompressedOracleDuality_LabelSymmetric_Supplement_MatchedLabels

open scoped BigOperators

namespace CompressedOracleDuality.LabelSymmetric.Supplement

/-- Lemma 5.8, (84), p.29: the full T<N/2 regime and the additive guessed-collision term. -/
theorem lemma_5_8 {n S T : ℕ} (B : ClassicalProgram n T)
    (hn : 6 ≤ n) (hS : n ≤ S) (hwidth : B.SpaceBound S)
    (hsym : ClassicalLabelSymmetric B) (hT : 2 * T < 2 ^ n) :
    classicalSuccess B ≤
      (1 + ∑ t : Fin T, ((injectiveLabels B t.castSucc).card : ℝ)) / (2 : ℝ) ^ n := by sorry

end CompressedOracleDuality.LabelSymmetric.Supplement
