-- Prove2me | Theorems.Thm_ARTreeCover_Supplement_theorem_39
-- name    : ARTreeCover.Supplement.theorem_39
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:12:51.349869+00:00
-- url     : https://prove2.me/theorems/948a4ea1-fcea-43d1-b265-14049643aa72
-- title:
--   Theorem 39 — connected $p$-path-separable graphs have almost-Ramsey embeddings into $\ell_q^{O(\log n)}$ satisfying $\Omega(n/(p\log n))$ vertices with stretch $O(1)$
-- statement:
--   There is an absolute constant $C>0$ such that for every real $\Delta>0$, every $q\in[1,\infty]$ and every connected $n$-vertex weighted $p$-path-separable graph $G$, there are a dimension $D\le C\,L(n)$, $L(n)=\max(1,\log_2n)$, and an almost-Ramsey embedding $f:V\to\ell_q^D$ for scale $\Delta$ satisfying at least
--   $$\frac{n}{C\,p\,L(n)}$$
--   vertices with distortion $C$.
--
--   Differences from the source:
--   - encoding: O(·) and Ω(·) → one absolute constant C > 0 chosen before every other quantifier; O(x) is C·x and Ω(x) is x/C; reason: the standard reading of asymptotic bounds with absolute constants; one constant for several O(·) is the same as several, since a larger C weakens every bound
--   - reading: log n inside the bound → L(n) = max(1, log₂ n); reason: equal to log₂ n for n ≥ 2; at n = 1 the printed log n is 0, which would make the bound 0 (or divide by 0) on a one-vertex graph
--   - encoding: ℓ_q^{O(log n)}, 1 ≤ q ≤ ∞ → PiLp q (Fin D → ℝ) with D ≤ C·L(n), q : ℝ≥0∞ with 1 ≤ q; reason: the same spaces; q = ∞ is the sup norm, and the dimension bound is uniform in q
--   - encoding: "for every real parameter ϵ > 0" (resp. 0 < ϵ ≤ 1) in the hypotheses → no ϵ binder; reason: ϵ does not occur in the conclusion, so the statement for every such ϵ is equivalent to the statement without it
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Theorem 39, p.50 (PDF p.53)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_logL
import Definitions.Def_ARTreeCover_Supplement_HasPathSep
import Definitions.Def_ARTreeCover_Supplement_IsAlmostRamseyEmbedding

open scoped ENNReal

namespace ARTreeCover.Supplement

open ARTreeCover

/-- **Theorem 39**, p.50 (PDF p.53). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"For every real parameters ∆, ϵ > 0 and 1 ≤ q ≤ ∞, any n-vertex connected p-path-separable graph G
admits an almost-Ramsey embedding f : V → ℓ_q^{O(log n)} for scale ∆, that satisfies Ω(n/(p log n))
vertices with stretch O(1)."

**Formalization Note.**
1. `O(x)` is `C · x` and `Ω(x)` is `x / C` with one absolute `C > 0` chosen before every other
   parameter. `L(n) = max(1, log₂ n)`. "Stretch" is the distortion of Definition 23.
2. `ℓ_q^{O(log n)}` is `PiLp q (fun _ : Fin D => ℝ)` with `D ≤ C · L(n)`, for every
   `q ∈ [1, ∞]` (`q : ℝ≥0∞` with `Fact (1 ≤ q)`, `q = ∞` the sup norm); the dimension bound is part of
   the conclusion and uniform in `q`.
3. The printed `ϵ > 0` does not occur in the conclusion; the binder is dropped (equivalent). -/
theorem theorem_39 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] (G : WGraph V) (p : ℕ) (Δ : ℝ),
        0 < Δ → G.graph.Connected → IsPPathSeparable G p false →
        (∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], ∃ D : ℕ, (D : ℝ) ≤ C * logL (Fintype.card V) ∧
            ∃ f : V → PiLp q (fun _ : Fin D => ℝ), IsAlmostRamseyEmbedding G f Δ ((Fintype.card V : ℝ) / (C * p * logL (Fintype.card V))) (C)) := by sorry

end ARTreeCover.Supplement
