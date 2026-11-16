-- Prove2me | Theorems.Thm_DOPriorityQueue_Construction_Supplement_lemma_6_3
-- name    : DOPriorityQueue.Construction.Supplement.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:42:56.314059+00:00
-- url     : https://prove2.me/theorems/b2065ce9-53a6-4fb6-847e-723d5564500e
-- title:
--   Lemma 6.3 — fixed-trace permutation support and entropy
-- statement:
--   Let $n\ge2$, $2n\le T$, $n\le U$ and $M\ge1$. Consider an exact, every-execution terminating online queue with $M$ private words, opaque one-word tokens arriving only at their insertions, and outputs supplied from private storage. Use the experiment $\sigma(X)$ of equation (7) with distinct fixed tokens and independent uniform priorities in $[n]$. For every fixed call-grouped server trace $v$ with $q$ probes, the set of output permutations from actual possible executions satisfies
--   $$|\operatorname{Perm}(v)|\le[2(M+2)]^{q+2n}.$$
--   Moreover, with $\Pi$ the stable output permutation and $P$ the random total probe count,
--   $$H(\Pi\mid V)\le(\mathbb E[P]+2n)\log_2(2(M+2)).$$
--   Support includes all possible executions, not merely positive-probability trace atoms or tapes. Local computations on priorities and metadata are arbitrary and free. Output identities remain private; traces contain only server addresses and read/write directions with call boundaries. No privacy, finite expectation or bounded trace-support assumption is imposed.
--
--   This is the routing support for Theorem 6.1. The first bound controls each individual fiber; the second averages those fiber bounds and permits infinite expected probes.
--
--   Differences from the source:
--   - generalization: the balls-and-bins model with w=Theta(log T) and M<=n/2 in the surrounding theorem → any word size and any M>=1 in the opaque controller model, also allowing atomic free numeric maps and public numeric initialization; reason: the routing argument uses only M resident words, token conservation, on-demand arrivals, private outputs and counted server accesses; the enlarged model includes source machines
--   - encoding: abstract distinct b_i and output permutations → injective natural token labels and lists of Fin n indices in stable output order; reason: opaque controllers cannot inspect labels or manufacture tokens, so this is only a relabeling
--   - encoding: conditional entropy in bits and an upper bound involving E[P] → countable conditional entropy and nonnegative extended expectation; reason: preserves infinite expected cost without adding integrability or finite support
-- source:
--   Zimai Guo, Cheng Hong, Zhechen Li, STOC 2027 submission #538 (October 2026), p. 29; proof pp. 29–30, Lemma 6.3

import Definitions.Def_DOPriorityQueue_Construction_Supplement_Opaque

set_option autoImplicit false

namespace DOPriorityQueue.Construction.Supplement

/-- Guo--Hong--Li, p. 29, Lemma 6.3, both (12) and (13).
No privacy or finite-expectation hypothesis is needed. -/
theorem lemma_6_3 (n T U M w : ℕ) (Q : OpaqueProgram w M) (b : Fin n → ℕ)
    (hn : 2 ≤ n) (hT : 2 * n ≤ T) (hU : n ≤ U) (hM : 1 ≤ M)
    (hb : Function.Injective b) (hcorrect : opaqueCorrect Q T U) :
    (∀ v : RAM.Trace w,
      (tracePermutations Q b v).card ≤ (2 * (M + 2)) ^ (probeCount v + 2 * n)) ∧
    residualEntropy (opaqueKernel Q) b ≤
      (mixedProbes (opaqueKernel Q) b + (2 * n : ℕ)) *
        ENNReal.ofReal (Real.logb 2 (2 * (M + 2 : ℕ))) := by sorry

end DOPriorityQueue.Construction.Supplement
