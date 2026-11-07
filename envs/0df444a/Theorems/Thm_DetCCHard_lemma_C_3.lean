-- Prove2me | Theorems.Thm_DetCCHard_lemma_C_3
-- name    : DetCCHard.lemma_C_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:38:23.643201+00:00
-- url     : https://prove2.me/theorems/19b7e574-b064-4560-b2f9-5630fe258430
-- title:
--   Lemma C.3 — short continuation: $2^b+1$ blocks force $d+1$ bits under (E) or (C)
-- statement:
--   Suppose $d \ge 2$ and $\mathcal P(M; x, d)$ with $0 < x \le 1$, and let $b \ge 0$ be an integer with $2^{b+1} x \le 1$. Consider an interlace of $M$ on a tuple list whose marginal is the column weights of $M$, and a restriction of it that retains at least $2^b + 1$ blocks, each of base row weight at least $2^{b+1} x$, and a label set $K$. Assume one of the following.
--
--   1. **(E)** The list is exactly 8-wise independent with weights $\nu$, and $\nu(K) \ge (9/25)\,2^{-b}$.
--   2. **(C)** The list is exactly 8192-wise independent with weights $\nu$, $\nu(Y) \ge v > 0$, the exceptional set $E$ is chosen from Lemma 6.10 with error bound $0 < \tau \le 1$, the retained blocks have indices outside $E$, $K \subseteq Y$, and $(\nu \mid Y)(K) \ge 2^{-b-1}$.
--
--   Then the restriction requires at least $d + 1$ bits.
--
--   The lemma is the last step of the weight-halving walks in Lemma 6.11, Theorem 6.12 and Theorem 7.2.
--
--   **Formalization Note** In (C) the exceptional set is any $E$ with $|E| \le e(v,\tau)$ and the total-variation bound of Lemma 6.10.
--
--   Differences from the source:
--   - generalization: "choose the exceptional set from Lemma 6.10" → every set E with |E| ≤ e(v, τ) and the total-variation bound of Lemma 6.10 for all J ⊆ [q] ∖ E with |J| ≤ 8; reason: the set the lemma provides is one of these, so the statement specializes to the paper's
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Lemma C.3, p.63

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_DetCCHard_commCost
import Definitions.Def_DetCCHard_IsWeight
import Definitions.Def_DetCCHard_DeletionBounds
import Definitions.Def_DetCCHard_TupleList
import Definitions.Def_DetCCHard_interlaceOn
import Definitions.Def_DetCCHard_epsVT

namespace DetCCHard

/-- **Lemma C.3 (short continuation)** (Gaspers–He–Mackenzie, arXiv:2508.05597, held version sha256
ad552d13…a4a03, Lemma C.3, p.63). Suppose `d ≥ 2` and `P(M; x, d)`, and let `b ≥ 0` be an integer
with `2^{b+1} x ≤ 1`. Consider an interlace of `M` on a tuple list whose marginal is the column
weights of `M`, and a restriction of it that retains at least `2^b + 1` blocks, each of base row
weight at least `2^{b+1} x`, and a label set `K`. Assume one of the following.
(E) The list is exactly 8-wise independent with weights `ν`, and `ν(K) ≥ (9/25) 2^{-b}`.
(C) The list is exactly 8192-wise independent with weights `ν`, `ν(Y) ≥ v > 0`, the exceptional
set is chosen from Lemma 6.10 with error bound `0 < τ ≤ 1`, the retained blocks have indices
outside that set, `K ⊆ Y`, and `(ν | Y)(K) ≥ 2^{-b-1}`.
Then the restriction requires at least `d + 1` bits.

**Formalization Note** In (C), "the exceptional set chosen from Lemma 6.10" is any set `E` with the
two properties that lemma asserts (`|E| ≤ e(v, τ)` and the total-variation bound for every
`J ⊆ [q] ∖ E` with `|J| ≤ 8`). The retained blocks are a set `S` of block indices. `x` is real
with `0 < x ≤ 1` (Definition 5.1); `q ≥ 1`. -/
theorem lemma_C_3 {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq Y] (M : X → Y → Bool)
    (μX : X → ℚ) (μY : Y → ℚ) (hμX : IsWeight μX) (hμY : IsWeight μY) (x : ℝ) (hx0 : 0 < x)
    (hx1 : x ≤ 1) (d : ℤ) (hd : 2 ≤ d) (hP : DeletionBounds M μX μY x d) (b : ℕ)
    (hbx : 2 ^ (b + 1) * x ≤ 1) {q : ℕ} (hq : 1 ≤ q) (T : TupleList Y (Fin q))
    (U : Set (Fin q × X)) (S : Finset (Fin q)) (hS : 2 ^ b + 1 ≤ S.card)
    (hSU : ∀ i ∈ S, 2 ^ (b + 1) * x ≤ (blockWt μX U i : ℝ)) (K : Set T.L)
    (hcase :
      (ExactlyIndep T 8 μY ∧ (9 / 25 : ℚ) * (1 / 2) ^ b ≤ wt T.ν K) ∨
      (ExactlyIndep T 8192 μY ∧ ∃ (Yev : Set T.L) (v τ : ℝ) (E : Finset (Fin q)),
        0 < v ∧ v ≤ (wt T.ν Yev : ℝ) ∧ 0 < τ ∧ τ ≤ 1 ∧ E.card ≤ eVT v τ ∧
        (∀ J : Finset (Fin q), Disjoint J E → J.card ≤ 8 →
          MarkovMixing.tvDist (condMarginal T.ν T.z Yev J) (prodMarginal μY J) ≤ epsVT v τ) ∧
        Disjoint S E ∧ K ⊆ Yev ∧ (1 / 2 : ℚ) ^ (b + 1) ≤ condWt T.ν Yev K)) :
    d + 1 ≤ (commCost (interlaceOn M T) U K : ℤ) := by sorry

end DetCCHard
