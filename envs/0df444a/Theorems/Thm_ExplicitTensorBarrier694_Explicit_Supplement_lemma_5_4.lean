-- Prove2me | Theorems.Thm_ExplicitTensorBarrier694_Explicit_Supplement_lemma_5_4
-- name    : ExplicitTensorBarrier694.Explicit.Supplement.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:42:26.782196+00:00
-- url     : https://prove2.me/theorems/84360960-41e6-4fde-87d3-5977b5d87e39
-- title:
--   Lemma 5.4 — vanishing of $c_J$ from $\sum_{i\notin I}c_{I\cup\{i\}}=0$
-- statement:
--   Let $p\ge1$ and $n=2p+1$. Suppose complex scalars $c_J$, indexed by the $(p+1)$-element subsets $J\subseteq[n]$, satisfy
--
--   $$\sum_{i\notin I}c_{I\cup\{i\}}=0\qquad\text{for every }p\text{-element subset }I\subseteq[n].$$
--
--   Then $c_J=0$ for every $(p+1)$-element subset $J$.
--
--   This combinatorial lemma is used in the proof of Theorem 5.2. This is a paper-proved result awaiting a formal proof.
--
--   Differences from the source:
--   - encoding: scalars c_J on the (p+1)-subsets of [n] → a function c on all subsets of Fin (2p+1), read only on (p+1)-subsets; reason: every insert i I with i ∉ I and card I = p has card p+1, and the conclusion concerns only (p+1)-subsets; the labels of [n] play no role
-- source:
--   Benjamin Lovitz, STOC 2027 submission #694 (October 2026), Lemma 5.4, p.16; standing context of §5, p.15 (PDF same); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/694.pdf

import Mathlib

open scoped BigOperators

namespace ExplicitTensorBarrier694.Explicit.Supplement

/-- Lovitz, STOC 2027 submission #694 (October 2026), Lemma 5.4, p.16 (standing context
of §5, p.15: n = 2p+1 ≥ 3). If scalars c_J indexed by the (p+1)-subsets of [n] satisfy
Σ_{i∉I} c_{I∪{i}} = 0 for all p-subsets I ⊆ [n], then every c_J = 0. The n elements of
[n] are indexed by `Fin (2p+1)`; `c` is read only on (p+1)-subsets. -/
theorem lemma_5_4 (p : ℕ) (hp : 1 ≤ p) (c : Finset (Fin (2 * p + 1)) → ℂ)
    (hc : ∀ I : Finset (Fin (2 * p + 1)), I.card = p →
      ∑ i ∈ Iᶜ, c (insert i I) = 0) :
    ∀ J : Finset (Fin (2 * p + 1)), J.card = p + 1 → c J = 0 := by sorry

end ExplicitTensorBarrier694.Explicit.Supplement
