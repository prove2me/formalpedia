-- Prove2me | Theorems.Thm_CompressedOracleDuality_LabelSymmetric_Supplement_lemma_5_6
-- name    : CompressedOracleDuality.LabelSymmetric.Supplement.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T22:08:48.369641+00:00
-- url     : https://prove2.me/theorems/a6017591-06cc-4e62-9529-7cd9b1653015
-- title:
--   Lemma 5.6 — matched-label set bound and both consequences
-- statement:
--   Let $N=2^n\ge64$, $S\ge n$, and $T\in\mathbb N$. Let $B$ be a deterministic label-symmetric $T$-query collision branching program with at most $2^S$ vertices in each internal layer and unrestricted finite output leaves. For every time $t<\min\{N/2,T\}$ and every reachable state $m$ in that layer, put $k=|L(m)|$, where $L$ is the minimum matched-label set derived from actual executions. Then
--   $$\binom Nk\le2^S,\qquad k>0\Longrightarrow k\log_2(N/k)\le S,$$
--   and
--   $$t\le\sqrt N\Longrightarrow k\le\frac{2S}{\log_2 N}.$$
--   The exact binomial estimate and both consequences are asserted together, including $k=0$ in the first and third conclusions. Label symmetry is required at every layer, including the terminal layer. This result constrains the number of labels supported by a reachable classical memory state.
--
--   Differences from the source:
--   - encoding: one carrier [N] for inputs and labels → published Fin (2^n) inputs and n-bit labels, identified by the fixed most-significant-bit-first bijection e; reason: e transports every oracle and label permutation bijectively; input ordering is the published strict order
--   - encoding: a singleton start layer, exactly 2^S internal vertices, and arbitrarily many terminal leaves → finite layer types with a Unique initial layer and at most 2^S vertices only for 1 <= t < T; reason: padding unreachable internal vertices recovers the printed width without altering executions, symmetry, or success; T=0 retains one fixed output
--   - encoding: the unique minimum matched set for t < N/2 → a minimum-cardinality selector for 2*t < 2^n, with empty-set totalization otherwise; reason: finiteness ensures a minimizer and label symmetry ensures uniqueness in the used regime; no matched-set property is assumed
--   - encoding: t < min{N/2,T} and t <= sqrt(N) → a time in Fin (T+1) with 2*t < 2^n and t < T, and the conditional t^2 <= 2^n; reason: these are equivalent inequalities for nonnegative integer times
--   - encoding: base-two log N in the denominator → n in the denominator, with n >= 6 and N=2^n; reason: log_2 N=n exactly; the logarithmic conclusion is conditional on k>0 to exclude division by zero
-- source:
--   Ding and Zhandry, Compressed Oracle Duality: A simple framework for knowing what quantum adversaries know, October 30, 2026 preprint, arXiv:submit/8306656 [quant-ph], STOC 2027 submission #94; source.pdf SHA-256 6614c6a707d45eff1e475fa25c9c0d22747adf304a0680ebf79d2bd118122daa; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/94.pdf, Lemma 5.6, (81) and both subsequent sentences, p.28; standing assumptions p.11

import Definitions.Def_CompressedOracleDuality_LabelSymmetric_Supplement_MatchedLabels

namespace CompressedOracleDuality.LabelSymmetric.Supplement

/-- Lemma 5.6, p.28: (81) and both subsequent consequences, including the k=0 case. -/
theorem lemma_5_6 {n S T : ℕ} (B : ClassicalProgram n T)
    (hn : 6 ≤ n) (hS : n ≤ S) (hwidth : B.SpaceBound S)
    (hsym : ClassicalLabelSymmetric B) (t : Fin (T + 1))
    (htN : 2 * t.val < 2 ^ n) (htT : t.val < T) (m : ReachableState B t) :
    Nat.choose (2 ^ n) (matchedLabels B t m).card ≤ 2 ^ S ∧
    (0 < (matchedLabels B t m).card →
      ((matchedLabels B t m).card : ℝ) *
        Real.logb 2 ((2 : ℝ) ^ n / ((matchedLabels B t m).card : ℝ)) ≤ (S : ℝ)) ∧
    (t.val ^ 2 ≤ 2 ^ n →
      ((matchedLabels B t m).card : ℝ) ≤ 2 * (S : ℝ) / (n : ℝ)) := by sorry

end CompressedOracleDuality.LabelSymmetric.Supplement
