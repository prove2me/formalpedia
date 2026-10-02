-- Prove2me | Theorems.Thm_AppliedComb_ManyFaces_covers_structure
-- name    : AppliedComb.ManyFaces.covers_structure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:46:52.053381+00:00
-- url     : https://prove2.me/theorems/ab572b99-d731-466e-9e52-6b66d71204e3
-- title:
--   Proposition 16.11 — the shape of a covering pair in P(t)
-- statement:
--   Let $V = (v_1, \dots, v_m)$ and $W = (w_1, \dots, w_n)$ be partitions of an integer $t$, ordered by partial sums as in the partial order on $\mathcal P(t)$, with $v_k = 0$ for $k > m$ and $w_k = 0$ for $k > n$. If $V$ covers $W$ in $\mathcal P(t)$, then $n \le m + 1$ and there are integers $i, j$ with $1 \le i < j \le n$ such that:
--
--   1. $v_\alpha = w_\alpha$ for $1 \le \alpha < i$;
--   2. $v_\beta = w_\beta$ for $j < \beta \le m$;
--   3. $v_i = 1 + w_i$;
--   4. either (a) $j \le m$ and $w_j = 1 + v_j$, or (b) $j = n = m + 1$ and $w_j = 1$;
--   5. if $j > i + 1$, then $w_\gamma = v_\gamma = v_i - 1$ for $i < \gamma < j$.
--
--   In words: $W$ is obtained from $V$ by moving a single unit from part $i$ to a later part $j$ (possibly a new last part of size $1$), and every part strictly between them equals $v_i - 1$.
--   $$W = (v_1, \dots, v_{i-1},\; v_i - 1,\; v_{i+1}, \dots, v_{j-1},\; v_j + 1,\; v_{j+1}, \dots).$$
--
--   This is the step used in the proof of the Gale–Ryser Theorem 16.12, which walks down a maximal chain from $R^d$ to $C$ one cover at a time.
--
--   **Formalization Note.** Partitions are lists satisfying `IsPartition t`; `entry V k` is the 1-based entry $v_k$. The hypotheses `IsPartition t V` and `IsPartition t W` repeat what `Covers t V W` already contains, as the book states them separately. The conclusion is the conjunction of $n \le m+1$ with the existence of $i, j$ satisfying items 1–5 exactly as printed. In item 5, $v_i - 1$ is natural-number subtraction, which is exact here because item 3 gives $v_i \ge 1$.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 324, Proposition 16.11

import Mathlib
import Definitions.Def_AppliedComb_ManyFaces_partitionDominance

namespace AppliedComb.ManyFaces

/-- Proposition 16.11 (Keller & Trotter, *Applied Combinatorics* (2017 Edition), p. 324).
Let `V = (v_1, …, v_m)` and `W = (w_1, …, w_n)` be partitions of `t`. If `V` covers `W` in `P(t)`,
then `n ≤ m + 1` and there are integers `1 ≤ i < j ≤ n` such that
1. `v_α = w_α` for `1 ≤ α < i`;
2. `v_β = w_β` for `j < β ≤ m`;
3. `v_i = 1 + w_i`;
4. either (a) `j ≤ m` and `w_j = 1 + v_j`, or (b) `j = n = m + 1` and `w_j = 1`;
5. if `j > i + 1`, then `w_γ = v_γ = v_i − 1` for `i < γ < j`.
Entries are 1-based (`entry V k = v_k`). -/
theorem covers_structure (t : ℕ) (V W : List ℕ) (hV : IsPartition t V) (hW : IsPartition t W)
    (hcov : Covers t V W) :
    W.length ≤ V.length + 1 ∧
      ∃ i j : ℕ, 1 ≤ i ∧ i < j ∧ j ≤ W.length ∧
        (∀ α : ℕ, 1 ≤ α → α < i → entry V α = entry W α) ∧
        (∀ β : ℕ, j < β → β ≤ V.length → entry V β = entry W β) ∧
        entry V i = 1 + entry W i ∧
        ((j ≤ V.length ∧ entry W j = 1 + entry V j) ∨
          (j = W.length ∧ W.length = V.length + 1 ∧ entry W j = 1)) ∧
        (i + 1 < j → ∀ γ : ℕ, i < γ → γ < j →
          entry W γ = entry V γ ∧ entry V γ = entry V i - 1) := by sorry

end AppliedComb.ManyFaces
