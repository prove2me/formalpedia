-- Prove2me | Theorems.Thm_DetCCHard_theorem_6_12
-- name    : DetCCHard.theorem_6_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:38:24.127669+00:00
-- url     : https://prove2.me/theorems/2c8d9dc0-edb8-4d4e-aff1-c16b83a14691
-- title:
--   Theorem 6.12 — surviving blocks outside the exceptional set and conditional label weight $1/2$ force cost $d + a$
-- statement:
--   Suppose $d \ge 2$ and $\mathcal P(M; x, d)$ with $0 < x \le 1$, and let an interlace of $M$ use an exactly 8192-wise independent tuple list with weights $\nu$ and the column weights of $M$ as marginal. Let $\nu(Y) \ge v > 0$, let $E$ be the exceptional set of Lemma 6.10 for $Y$ with any error bound $0 < \tau \le 1$, and let an integer $a \ge 1$ satisfy $2^a x \le 1$. If a restriction retains at least $2^{a-1}+1$ blocks indexed outside $E$, each of base row weight at least $2^a x$, and a column set $K \subseteq Y$ with $(\nu \mid Y)(K) \ge 1/2$, then its cost is at least
--   $$
--   d + a .
--   $$
--
--   This extends Lemma 6.11 to label sets of small weight, which arise after a protocol prefix.
--
--   **Formalization Note** The exceptional set is any $E$ with $|E| \le e(v,\tau)$ and the total-variation bound of Lemma 6.10 for every $J \subseteq [q] \setminus E$ with $|J| \le 8$.
--
--   Differences from the source:
--   - generalization: "choose the exceptional set from Lemma 6.10" → every set E with |E| ≤ e(v, τ) and the total-variation bound of Lemma 6.10 for all J ⊆ [q] ∖ E with |J| ≤ 8; reason: the set the lemma provides is one of these, so the statement specializes to the paper's
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Theorem 6.12, p.27

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_DetCCHard_commCost
import Definitions.Def_DetCCHard_IsWeight
import Definitions.Def_DetCCHard_DeletionBounds
import Definitions.Def_DetCCHard_TupleList
import Definitions.Def_DetCCHard_interlaceOn
import Definitions.Def_DetCCHard_epsVT

namespace DetCCHard

/-- **Theorem 6.12 (Surviving blocks after conditioning)** (Gaspers–He–Mackenzie,
arXiv:2508.05597, held version sha256 ad552d13…a4a03, Theorem 6.12, p.27). Suppose `d ≥ 2` and
`P(M; x, d)`, and let an interlace of `M` use an exactly 8192-wise independent tuple list with
weights `ν` and the column weights of `M` as marginal. Let `ν(Y) ≥ v > 0`, choose the exceptional
set `E` of Lemma 6.10 with any error bound `0 < τ ≤ 1`, and let an integer `a ≥ 1` satisfy
`2^a x ≤ 1`. If a restriction retains at least `2^{a−1} + 1` blocks indexed outside `E`, each of
base row weight at least `2^a x`, and a column set `K ⊆ Y` with `(ν | Y)(K) ≥ 1/2`, then its cost
is at least `d + a`.

**Formalization Note** "The exceptional set from Lemma 6.10" is any set `E` with the two properties
that lemma asserts: `|E| ≤ e(v, τ)` and the total-variation bound `ε(v, τ)` for every `J ⊆ [q] ∖ E`
with `|J| ≤ 8`. The restriction is `U × K`; the retained blocks are a set `S` of block indices
disjoint from `E`. `x` is real with `0 < x ≤ 1` (Definition 5.1); `q ≥ 1`. -/
theorem theorem_6_12 {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq Y] (M : X → Y → Bool)
    (μX : X → ℚ) (μY : Y → ℚ) (hμX : IsWeight μX) (hμY : IsWeight μY) (x : ℝ) (hx0 : 0 < x)
    (hx1 : x ≤ 1) (d : ℤ) (hd : 2 ≤ d) (hP : DeletionBounds M μX μY x d) {q : ℕ} (hq : 1 ≤ q)
    (T : TupleList Y (Fin q)) (hT : ExactlyIndep T 8192 μY) (Yev : Set T.L) (v : ℝ)
    (hv0 : 0 < v) (hY : v ≤ (wt T.ν Yev : ℝ)) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (E : Finset (Fin q)) (hEcard : E.card ≤ eVT v τ)
    (hE : ∀ J : Finset (Fin q), Disjoint J E → J.card ≤ 8 →
      MarkovMixing.tvDist (condMarginal T.ν T.z Yev J) (prodMarginal μY J) ≤ epsVT v τ)
    (a : ℕ) (ha : 1 ≤ a) (hax : 2 ^ a * x ≤ 1) (U : Set (Fin q × X)) (S : Finset (Fin q))
    (hSE : Disjoint S E) (hS : 2 ^ (a - 1) + 1 ≤ S.card)
    (hSU : ∀ i ∈ S, 2 ^ a * x ≤ (blockWt μX U i : ℝ)) (K : Set T.L) (hKY : K ⊆ Yev)
    (hK : (1 / 2 : ℚ) ≤ condWt T.ν Yev K) :
    d + a ≤ (commCost (interlaceOn M T) U K : ℤ) := by sorry

end DetCCHard
