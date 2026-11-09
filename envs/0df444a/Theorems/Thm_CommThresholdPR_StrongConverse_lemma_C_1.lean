-- Prove2me | Theorems.Thm_CommThresholdPR_StrongConverse_lemma_C_1
-- name    : CommThresholdPR.StrongConverse.lemma_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:40.124193+00:00
-- url     : https://prove2.me/theorems/6b168d83-7323-4ea2-8a32-99fefa7d01fc
-- title:
--   Lemma C.1 — exact simultaneous finite correlated sampling
-- statement:
--   Let $\{D_i\}_{i\in I}$ be any finite family of distributions on a finite set $V$. There is one finite-valued shared seed $S$ and functions $f_i$ such that $f_i(S)$ has exactly law $D_i$, simultaneously for the entire family, and for every $i,j$,
--   $$\Pr[f_i(S)\ne f_j(S)]\le\frac{2\operatorname{TV}(D_i,D_j)}{1+\operatorname{TV}(D_i,D_j)}\le2\operatorname{TV}(D_i,D_j).$$
--   The family may be empty. No nonemptiness of $V$ is required when the family is empty. This is an exact common-seed sampler rather than an approximate or pair-specific coupling.
--
--   Differences from the source:
--   - encoding: a finite family of laws and a finite-valued shared random variable → a Fintype-indexed family, a PMF on Fin k and a family of sample functions; reason: arbitrary finite alphabets can be relabeled by Fin k; an empty index family admits a Unit-sized seed even when V is empty
-- source:
--   Daiki Suruga, The Exact Communication Threshold for Parallel Repetition, STOC 2027 submission #304 (October 2026), Lemma C.1, pp. 33–34, (66), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/304.pdf

import Definitions.Def_CommThresholdPR_StrongConverse_Simulation

namespace CommThresholdPR.StrongConverse

theorem lemma_C_1 {I V : Type} [Fintype I] [Fintype V] (D : I → PMF V) :
    ∃ (k : ℕ) (seed : PMF (Fin k)) (S : I → Fin k → V),
      (∀ i, seed.map (S i) = D i) ∧
      ∀ i j, prob seed (fun r => S i r ≠ S j r) ≤
          2 * tv (D i) (D j) / (1 + tv (D i) (D j)) ∧
        2 * tv (D i) (D j) / (1 + tv (D i) (D j)) ≤ 2 * tv (D i) (D j) := by sorry

end CommThresholdPR.StrongConverse
