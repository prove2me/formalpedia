-- Prove2me | Theorems.Thm_DetCCHard_lemma_6_11
-- name    : DetCCHard.lemma_6_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:38:28.884625+00:00
-- url     : https://prove2.me/theorems/7d954eb1-9093-4673-b27f-139d943dba9c
-- title:
--   Lemma 6.11 — $2^{a-1}+1$ surviving blocks and label weight $9/25$ force cost $d + a$
-- statement:
--   Suppose $d \ge 2$ and $\mathcal P(M; x, d)$ with $0 < x \le 1$. Let an interlace of $M$ use a tuple list (of length $q \ge 1$) that is exactly 8-wise independent with the column weights of $M$ as marginal. If an integer $a \ge 1$ satisfies $2^a x \le 1$, and a restriction retains at least $2^{a-1} + 1$ blocks, each of base row weight at least $2^a x$, together with a label set of total weight at least $9/25$, then the restricted interlace has cost at least
--   $$
--   d + a .
--   $$
--
--   This is the lower bound for restrictions of interlaces on 8-wise independent lists that the template layer and Theorem A.3 build on.
--
--   **Formalization Note** The restriction is $U \times K$; the retained blocks are a set $S$ of block indices with $|S| \ge 2^{a-1} + 1$, each keeping base row weight at least $2^a x$.
--
--   Differences from the source:
--   none.
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Lemma 6.11, pp.26–27

import Mathlib
import Definitions.Def_DetCCHard_commCost
import Definitions.Def_DetCCHard_IsWeight
import Definitions.Def_DetCCHard_DeletionBounds
import Definitions.Def_DetCCHard_TupleList
import Definitions.Def_DetCCHard_interlaceOn

namespace DetCCHard

/-- **Lemma 6.11 (Surviving blocks in a tuple list)** (Gaspers–He–Mackenzie, arXiv:2508.05597,
held version sha256 ad552d13…a4a03, Lemma 6.11, pp.26–27). Suppose `d ≥ 2` and `P(M; x, d)`. Let
an interlace of `M` use a tuple list that is exactly 8-wise independent with the column weights of
`M` as marginal. If an integer `a ≥ 1` satisfies `2^a x ≤ 1`, and a restriction retains at least
`2^{a−1} + 1` blocks, each of base row weight at least `2^a x`, together with a label set of total
weight at least `9/25`, then the restricted interlace has cost at least `d + a`.

**Formalization Note** The restriction is `U × K` with `U` a set of interlace rows and `K` a set of
labels; "retains at least `2^{a−1} + 1` blocks" is a set `S` of block indices of that size each of
whose blocks keeps base row weight (`blockWt`, no division by `q`) at least `2^a x`. `x` is real
with `0 < x ≤ 1` (Definition 5.1); tuple length `q ≥ 1` (Definition 4.4). -/
theorem lemma_6_11 {X Y : Type} [Fintype X] [Fintype Y] (M : X → Y → Bool) (μX : X → ℚ)
    (μY : Y → ℚ) (hμX : IsWeight μX) (hμY : IsWeight μY) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (d : ℤ) (hd : 2 ≤ d) (hP : DeletionBounds M μX μY x d) {q : ℕ} (hq : 1 ≤ q)
    (T : TupleList Y (Fin q)) (hT : ExactlyIndep T 8 μY) (a : ℕ) (ha : 1 ≤ a)
    (hax : 2 ^ a * x ≤ 1) (U : Set (Fin q × X)) (K : Set T.L) (S : Finset (Fin q))
    (hS : 2 ^ (a - 1) + 1 ≤ S.card) (hSU : ∀ i ∈ S, 2 ^ a * x ≤ (blockWt μX U i : ℝ))
    (hK : (9 / 25 : ℚ) ≤ wt T.ν K) :
    d + a ≤ (commCost (interlaceOn M T) U K : ℤ) := by sorry

end DetCCHard
