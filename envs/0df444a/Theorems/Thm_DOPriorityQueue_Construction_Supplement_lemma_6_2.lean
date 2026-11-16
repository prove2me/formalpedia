-- Prove2me | Theorems.Thm_DOPriorityQueue_Construction_Supplement_lemma_6_2
-- name    : DOPriorityQueue.Construction.Supplement.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:42:17.039793+00:00
-- url     : https://prove2.me/theorems/d93c8968-2058-46c0-b465-abe552106b27
-- title:
--   Lemma 6.2 — residual permutation entropy, including encoded payloads
-- statement:
--   Let $n\ge2$, $2n\le T$ and $n\le U$. Fix distinct tokens $b_1,\ldots,b_n$. Choose $X_i$ independently and uniformly in $[n]$ and let $\sigma(X)$ insert all $(X_i,b_i)$ and then extract $n$ times. Let $\Pi$ be the stable sorting permutation of $(X_i,i)$ and let $V$ be the observed call-grouped server trace. For a normalized trace mechanism with insertion-field replacement $(\varepsilon,\delta)$ differential privacy, where $\varepsilon\ge0$ and $0\le\delta\le1$, set
--   $$\gamma_n=\frac{\varepsilon+1}{\ln2}+\frac{\delta\log_2n}{1-e^{-1}}.$$
--   Then, in bits,
--   $$H(\Pi\mid V)\ge n(\log_2n-2-\gamma_n).$$
--   The law includes both independent priorities and internal randomization. This statement holds without payload indivisibility, private-space bounds, finite trace support, finite expected probes or a bounded worst-case probe assumption. For an exact queue its output permutation is exactly $\Pi$. The lemma is the information-theoretic support for Theorem 6.1.
--
--   Differences from the source:
--   - generalization: the trace law of an exact priority queue, also allowing encoded payloads → any normalized insertion-private trace kernel, with Pi defined by stable sorting of the input; reason: exactness identifies actual queue outputs with this deterministic Pi; no execution or routing hypothesis is used by the entropy argument
--   - encoding: one-based indices and distinct abstract tokens → Fin n indices, priorities X_i.val+1 and injective natural token labels; reason: relabeling preserves independent uniform priorities, ties, adjacency and entropy
--   - encoding: real finite conditional entropy and possibly negative lower bound → extended nonnegative entropy, and ofReal of the lower bound; reason: the normalized law and finite permutation range imply finite entropy; a negative bound is equivalent to zero for a nonnegative entropy
-- source:
--   Zimai Guo, Cheng Hong, Zhechen Li, STOC 2027 submission #538 (October 2026), p. 28; proof pp. 28–29, Lemma 6.2

import Definitions.Def_DOPriorityQueue_Construction_Supplement_Experiment

set_option autoImplicit false

namespace DOPriorityQueue.Construction.Supplement

/-- Guo--Hong--Li, p. 28, Lemma 6.2 (8), including its final sentence.
The kernel need not come from an opaque-payload or space-bounded implementation. -/
theorem lemma_6_2 (n T U w : ℕ) (K : TraceKernel w) (b : Fin n → ℕ)
    (ε δ : ℝ) (hn : 2 ≤ n) (hT : 2 * n ≤ T) (hU : n ≤ U)
    (hb : Function.Injective b) (hprivacy : insertionDO K T U ε δ) :
    ENNReal.ofReal ((n : ℝ) * (Real.logb 2 n - 2 - gamma n ε δ)) ≤
      residualEntropy K b := by sorry

end DOPriorityQueue.Construction.Supplement
