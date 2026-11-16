-- Prove2me | Theorems.Thm_ARTreeCover_Supplement_theorem_38
-- name    : ARTreeCover.Supplement.theorem_38
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:12:13.242433+00:00
-- url     : https://prove2.me/theorems/4b13c612-1c1e-42fd-8bbb-8ea9ca58d75e
-- title:
--   Theorem 38 — connected graphs have almost-Ramsey embeddings into $\ell_q^{O(\log n)}$ satisfying $\Omega(n^{1-1/k}/k)$ vertices with distortion $O(k)$
-- statement:
--   There is an absolute constant $C>0$ such that for every real $\Delta>0$, every $q\in[1,\infty]$, every integer $k>0$ and every connected $n$-vertex weighted graph $G$, there are a dimension $D\le C\,L(n)$, $L(n)=\max(1,\log_2n)$, and an almost-Ramsey embedding $f:V\to\ell_q^D$ for scale $\Delta$ satisfying at least
--   $$\frac{n^{1-1/k}}{Ck}$$
--   vertices with distortion $Ck$.
--
--   Differences from the source:
--   - encoding: O(·) and Ω(·) → one absolute constant C > 0 chosen before every other quantifier; O(x) is C·x and Ω(x) is x/C; reason: the standard reading of asymptotic bounds with absolute constants; one constant for several O(·) is the same as several, since a larger C weakens every bound
--   - reading: log n inside the bound → L(n) = max(1, log₂ n); reason: equal to log₂ n for n ≥ 2; at n = 1 the printed log n is 0, which would make the bound 0 (or divide by 0) on a one-vertex graph
--   - encoding: ℓ_q^{O(log n)}, 1 ≤ q ≤ ∞ → PiLp q (Fin D → ℝ) with D ≤ C·L(n), q : ℝ≥0∞ with 1 ≤ q; reason: the same spaces; q = ∞ is the sup norm, and the dimension bound is uniform in q
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Theorem 38, p.50 (PDF p.53)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_logL
import Definitions.Def_ARTreeCover_Supplement_IsAlmostRamseyEmbedding

open scoped ENNReal

namespace ARTreeCover.Supplement

open ARTreeCover

/-- **Theorem 38**, p.50 (PDF p.53). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"For every real parameters ∆ > 0 and 1 ≤ q ≤ ∞, and for every integer parameter k > 0, any n-vertex
undirected weighted connected graph G admits an almost-Ramsey embedding f : V → ℓ_q^{O(log n)} for
scale ∆, that satisfies Ω(1/k · n^{1−1/k}) vertices with distortion O(k)."

**Formalization Note.**
1. `O(x)` is `C · x` and `Ω(x)` is `x / C` with one absolute `C > 0` chosen before every other
   parameter. `L(n) = max(1, log₂ n)`.
2. `ℓ_q^{O(log n)}` is `PiLp q (fun _ : Fin D => ℝ)` with `D ≤ C · L(n)`, for every
   `q ∈ [1, ∞]` (`q : ℝ≥0∞` with `Fact (1 ≤ q)`, `q = ∞` the sup norm); the dimension bound is part of
   the conclusion and uniform in `q`. -/
theorem theorem_38 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] (G : WGraph V) (Δ : ℝ) (k : ℕ),
        0 < Δ → 0 < k → G.graph.Connected →
        (∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], ∃ D : ℕ, (D : ℝ) ≤ C * logL (Fintype.card V) ∧
            ∃ f : V → PiLp q (fun _ : Fin D => ℝ), IsAlmostRamseyEmbedding G f Δ ((Fintype.card V : ℝ) ^ (1 - ((1 : ℝ) / k)) / (C * k)) (C * k)) := by sorry

end ARTreeCover.Supplement
