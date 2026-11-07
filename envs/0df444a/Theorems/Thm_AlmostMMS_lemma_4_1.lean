-- Prove2me | Theorems.Thm_AlmostMMS_lemma_4_1
-- name    : AlmostMMS.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:49:48.577259+00:00
-- url     : https://prove2.me/theorems/d7989afb-96c0-473d-abff-eb71f224a2ca
-- title:
--   Lemma 4.1 — saved items
-- statement:
--   Let $\varepsilon\in(0,1)$ and let $r_1,C_1\ge2$, $r_1\le m$ be integers. There are a set $W\subseteq N$ with $|W|\le\varepsilon n/8$, a set $S\subseteq M$ with
--   $$
--   r_1\le|S|\le2q^2C_1^{8q^2/\varepsilon}r_1
--   $$
--   that is a union of $t\le2q^2$ maximal consecutive intervals and contains the first item, and an integer $\eta\ge\frac{C_1-1}{2q^2}|S|$, such that the following holds. For every $i\in N-W$ and $\alpha\in Q$ whose breakpoint $\ell=m_i(\alpha)$ belongs to $E=M-S$: $\ell\ge\eta$, the items $\ell-\eta+1,\dots,\ell$ belong to $E$, and the interval $(\ell-\eta,\ell]$ contains at most $n/2$ breakpoint occurrences.
--
--   The saved set $S$ creates a breakpoint-free buffer in $E$, so that the demands of the agents outside $W$ are well spread over $E$.
--
--   Differences from the source:
--   - reading: W ⊂ N, S ⊂ M → W ⊆ N, S ⊆ M, so that W = ∅ and S = M are allowed; reason: the proof's W may be empty and its S may exhaust M, e.g. when r₁ = m
--   - encoding: S of the form of a union of t maximal intervals → the cardinality bound on `protectedPrefixes S`, which has one element per maximal interval; reason: every set of items has a unique such decomposition
--   - encoding: "ℓ belongs to E" with one-based ℓ → an item e ∉ S with e.val + 1 = ℓ; reason: positions are zero-based in `Fin m`
--   - encoding: §§3–5's standing ordered instance with MMS bundles of value 1 → a structure `J : OrderedInstance n m d`; reason: the structure holds exactly Assumption 1's three bullets
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Lemma 4.1, p.32

import Mathlib
import Definitions.Def_AlmostMMS_OrderedInstance
import Definitions.Def_AlmostMMS_IsSavedSplit

namespace AlmostMMS

open Finset

/-- **Lemma 4.1 (Saved items), p.32.** Feige, Grinberg, *Almost-MMS allocations with small agent redundancy*, STOC 2027 submission,
arXiv:2611.05360 (manuscript sha256 3925c4ab…): let `ε ∈ (0, 1)` and let `r₁, C₁ ≥ 2`, `r₁ ≤ m` be
integers. There are `W ⊆ N` with `|W| ≤ εn/8`, a set `S ⊆ M` of size
`r₁ ≤ |S| ≤ 2q²C₁^{8q²/ε} r₁` that is a union of `t ≤ 2q²` maximal consecutive intervals and contains the
first item, and an integer `η ≥ ((C₁ - 1)/(2q²)) |S|`, with the breakpoint property recorded in
`IsSavedSplit`.

**Formalization Note.** The exponent `8q²/ε` is real (`Real.rpow`). Every subset of the items is uniquely
a union of maximal consecutive intervals, so "of the form" contributes only the count `t`, the cardinality
of `protectedPrefixes S`. The printed `⊂` allows `W = ∅` and `S = M`. -/
theorem lemma_4_1 {n m d q : ℕ} (hq : 3 ≤ q) (J : OrderedInstance n m d) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) (r₁ C₁ : ℕ) (hr : 2 ≤ r₁) (hC : 2 ≤ C₁) (hrm : r₁ ≤ m) :
    ∃ (W : Finset (Fin n)) (S : Finset (Fin m)) (η : ℕ),
      (W.card : ℝ) ≤ ε * (n : ℝ) / 8 ∧
      r₁ ≤ S.card ∧
      (S.card : ℝ) ≤ 2 * (q : ℝ) ^ 2 * (C₁ : ℝ) ^ (8 * (q : ℝ) ^ 2 / ε) * (r₁ : ℝ) ∧
      (protectedPrefixes S).card ≤ 2 * q ^ 2 ∧
      ((C₁ : ℝ) - 1) / (2 * (q : ℝ) ^ 2) * (S.card : ℝ) ≤ (η : ℝ) ∧
      IsSavedSplit J.v q W S η := by sorry

end AlmostMMS
